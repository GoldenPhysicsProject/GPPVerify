#!/usr/bin/env python3
"""Catch declarations that assert nothing but do not look like `True`-stubs.

## Why a third vacuity gate

`check_stub_naming.py` already catches two shapes:

* `theorem foo : True := trivial` — the honest, counted parking convention;
* `theorem foo : X = X := rfl` — reflexivity tautology, added 2026-09-01 after eleven turned
  up, including `three_generations : (3 : ℕ) = 3`.

Both key on the conclusion being visibly empty. On 2026-09-02 a **clean** rebuild of the tree
emitted 21 unused-binder warnings, and reading them turned up four more declarations that
assert nothing — none visible to either gate, because in each case the conclusion is an
ordinary proposition and the emptiness lives elsewhere:

    lemma shadow_exact_implies_c0 (c : ℝ) (h_shadow : c = 0) : c = 0 := h_shadow
      -- "The shadow breaking condition: c_2D = 0 forces scale invariance."
      -- The identity function. Conclusion and hypothesis are the same proposition.

    lemma shadow_coupling_sq_rational (k N : ℤ) :
        ∃ q : ℚ, q = shadowCoupling k N ^ 2 := ⟨_, rfl⟩
      -- shadowCoupling is already ℚ-valued: `X = X` wearing a quantifier.

    theorem rh_no_zeros_on_imaginary_axis (rh : RiemannHypothesis) (s : ℂ)
        (hzero : riemannZeta s = 0) (hs_re : s.re = 0) : ¬(0 < s.re ∧ s.re < 1)
      -- "Under RH: the imaginary axis has no non-trivial zeros."
      -- Proof used neither `rh` nor `hzero`. It is ¬(0 < 0).

    lemma boltzmann_relic_form (m T_freeze M_Pl : ℝ) (hm : m > 0) … : ∃ Omega : ℝ, Omega > 0
      := ⟨1, one_pos⟩
      -- "Relic abundance scales with shadow breaking via Boltzmann suppression."
      -- Asserts that a positive real number exists.

## What this checks — two rules, both sound

1. **`conclusion-is-hypothesis`** — the conclusion is character-identical to one of the
   declaration's own hypotheses, so the declaration is the identity function: it transports
   no information and could not have failed.

2. **`existential-reflexivity`** — the conclusion is `∃ x : T, x = e` (or `e = x`) with `e`
   free of `x`, so `⟨e, rfl⟩` proves it. Reflexivity under a quantifier.

## What this does NOT check, and why — two rules tried and withdrawn

The last two examples above are the interesting ones, and **this gate cannot see either**.
Both were attempted and both were wrong; recording the failures is worth more than the
retraction, because the shapes look catchable and the next session will think of them again:

* *"A data binder (`ℝ`, `ℂ`, `ℕ`, …) that the conclusion never mentions."* Reported **173**
  declarations, essentially all correct mathematics. A binder is routinely used in *another
  binder's type* rather than in the conclusion — `{ι κ : Type}` appearing only in
  `c : ι → κ`, a dimension `{n : ℕ}` appearing only in `z : Fin n → ℂ`. That is how index
  types and dimensions are written, not a defect.

* *"The conclusion mentions none of the binders, so it is closed."* Narrower, and still
  wrong: it flagged `rh_of_atomWeightOne (h : AtomWeightOne) : RiemannHypothesisStrip`.
  An implication between two named `Prop`s has a closed conclusion and is exactly the shape
  a good conditional theorem takes. What made `boltzmann_relic_form` empty was not closure
  but *triviality* — the conclusion is provable from nothing — and triviality is not
  syntactically decidable.

**The signal that does catch these is Lean's own `unusedVariables` warning**, which is why
all four were found on 2026-09-02 and not before. It has one hole, the same one documented at
length in `check_sorries.py`: a module replayed from cache emits no diagnostic, so on a warm
build the warnings simply are not there. `build.yml` therefore deletes `.lake/build` (this
package's artifacts only — Mathlib's cache lives under `.lake/packages/` and is untouched)
before building, so every CI run elaborates the whole tree fresh, and then fails on any
unused binder. That is the real gate for this class. This script is its source-level
complement for the two shapes a compiler will never complain about, because both type-check
perfectly well.

An exclusion is fine when argued for — add the declaration name to `ALLOWED` below with a
reason. An accidental vacuity is the bug; a reviewed one is not.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_stub_naming import STUB, strip_comments, declarations, _split_top  # noqa: E402

# Declarations deliberately exempt, each with a stated reason.
# Empty by design: every exemption should be argued for in review, not inherited silently.
ALLOWED: dict[str, str] = {}

OPEN, CLOSE = "([{⟨", ")]}⟩"
IDENT = re.compile(r"[^\W\d][\w'!?₀-₉]*", re.UNICODE)


def split_statement(flat: str) -> tuple[str, str] | None:
    """Return (signature, conclusion) for a flattened declaration, or None if unparseable.

    `let` in a statement puts both a `:` and a `:=` into the conclusion and defeats the
    splits below. Rather than parse Lean, skip those: a gate that guesses is worse than one
    that admits what it cannot see.
    """
    if re.search(r"\blet\b", flat):
        return None
    sig, rest = _split_top(flat, " : ")
    if rest is None:
        return None
    concl, _ = _split_top(rest, " := ")
    if concl is None:
        concl, _ = _split_top(rest, ":= by")
    if concl is None:
        return None
    return sig, concl.strip()


def binder_types(sig: str) -> list[str]:
    """Types of the signature's bracketed binders.

    Scans with a depth counter rather than a regex: a binder type routinely contains
    parentheses (`{S : Set (PadicInt p)}`), and a regex that excludes them silently drops
    exactly those binders — which is how an earlier draft of this gate reported a theorem
    as having a closed conclusion when the conclusion named a binder it had failed to see.
    """
    types: list[str] = []
    i = 0
    while i < len(sig):
        if sig[i] in OPEN:
            depth, j = 1, i + 1
            while j < len(sig) and depth:
                if sig[j] in OPEN:
                    depth += 1
                elif sig[j] in CLOSE:
                    depth -= 1
                j += 1
            _names, ty = _split_top(sig[i + 1:j - 1], " : ")
            if ty is not None:
                types.append(ty.strip())
            i = j
        else:
            i += 1
    return types


def existential_reflexivity(concl: str) -> bool:
    """`∃ x : T, x = e` / `∃ x : T, e = x` with `e` free of `x`."""
    m = re.match(r"^∃\s*([^\W\d][\w']*)\s*:\s*[^,]+,\s*(.*)$", concl, re.UNICODE)
    if not m:
        return False
    var, body = m.group(1), m.group(2).strip()
    lhs, rhs = _split_top(body, " = ")
    if lhs is None:
        return False
    lhs, rhs = lhs.strip(), rhs.strip()
    return any(a == var and var not in IDENT.findall(b)
               for a, b in ((lhs, rhs), (rhs, lhs)))


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    root = repo / "GppVerify"
    findings: list[tuple[str, str, str]] = []

    for path in sorted(root.rglob("*.lean")):
        src = strip_comments(path.read_text())
        for name, lineno, flat in declarations(src):
            if STUB.search(flat) or name in ALLOWED:
                continue
            parts = split_statement(flat)
            if parts is None:
                continue
            sig, concl = parts
            where = f"{path.relative_to(repo)}:{lineno}: {name}"

            if concl in binder_types(sig):
                findings.append(
                    (where, "conclusion-is-hypothesis",
                     f"the conclusion `{concl}` is one of its own hypotheses — this is the "
                     "identity function and could not have failed")
                )
            elif existential_reflexivity(concl):
                findings.append(
                    (where, "existential-reflexivity",
                     f"`{concl[:80]}` is proved by `⟨e, rfl⟩` — reflexivity under a "
                     "quantifier, asserting nothing")
                )

    if findings:
        print(f"::error::{len(findings)} declaration(s) assert nothing.")
        print("Each is true no matter what, under a name that reads as a real result.")
        print("Either state what the name claims, or park it honestly as an")
        print("`open_… : True := trivial` stub so that it is counted:\n")
        for where, kind, why in findings:
            print(f"  [{kind}] {where}")
            print(f"      {why}")
        return 1

    print("No vacuous declarations (conclusion-is-hypothesis, existential-reflexivity).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
