#!/usr/bin/env python3
"""Enforce the open_-prefix convention on `True`-stubs, and publish an honest count.

This repository parks an open result as `theorem foo : True := trivial` (or
`∀ (_ : True), True`). That is the honest convention -- far better than a `sorry` or an
axiom asserting the open claim -- but it has one sharp edge: a stub reports "does not
depend on any axioms", the cleanest possible bill of health, **while asserting nothing**.
A file full of stubs shows 0 sorry / 0 axiom and can read as fully proved when it is not.

Until 2026-08-30 that edge had actually cut: the repo contained, among others,

    theorem yang_mills_mass_gap : True := trivial
    theorem yang_mills_existence : True := trivial
    theorem weil_criterion : True := trivial
    theorem os_reconstruction : True := trivial

-- Millennium-Prize-scale problems and major open results, carrying the names of the
theorems they are *not*, in a tree advertising zero sorries and zero axioms. Nothing was
being smuggled into a proof (a `True` stub is inert, and none of these were referenced by
real content), but anyone grepping the source could reasonably have concluded otherwise.

The fix is structural rather than editorial: every stub name must begin with `open_`, so
the name itself says the result is open, and this gate makes a non-conforming stub fail
CI. `open_yang_mills_mass_gap : True := trivial` cannot be misread.

## Why this script was rewritten (2026-08-31)

The first version of this gate matched **line by line**: it remembered the most recent
`theorem`/`lemma` line, then looked for `: True := trivial` on some later line. That
misses a stub written like this --

    theorem shadow_discontinuity :
        -- Disc(celestial amplitude) = shadow transform jump = loop integrand
        True := trivial

-- because the line carrying `True := trivial` has no `:` in front of `True` (the colon
is two lines up, separated by a comment). Eight stubs were invisible to the gate for
exactly this reason, and **all eight were unprefixed**, including
`shadow_discontinuity`, `born_rule_from_haar`, `meyer_spectral_weil` and
`adelic_l2_regularization`. The gate reported "All True-stubs correctly prefixed" while
the very names it exists to catch sat in the tree, and the published count was 142 when
the real number was 150.

So the gate no longer reads lines. It strips Lean comments first (both `--` and `/- -/`,
nested), splits the source into whole declarations, and tests each declaration as a unit.
A stub cannot hide behind a comment in the middle of its own statement.

Exit 1 (failing the build) if any `True`-stub declaration lacks the prefix, or if the
count stated in the blueprint has drifted from the real one.
"""

import re
import sys
from pathlib import Path

# A declaration starts at column 0 with one of these keywords (or an attribute that
# precedes one). Anything indented is inside the declaration we are already in.
DECL_START = re.compile(
    r"^(?:@\[|theorem|lemma|def|noncomputable|instance|structure|inductive|abbrev|example|"
    r"class|opaque|axiom)\b",
    re.M,
)
NAME = re.compile(r"^(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'!?]*)")

# Applied to a whole declaration with comments already stripped and whitespace flattened.
#
# A stub is any declaration whose *conclusion* is `True` and whose proof is trivial-equivalent.
# Both halves need to be permissive, and each was widened after a stub slipped through:
#
#   `theorem foo : True := trivial`                     -- the original shape
#   `theorem foo : ∀ (_ : True), True := by intro; trivial`
#   `theorem foo : ∀ (_ : ℂ), True := fun _ => trivial` -- binder is NOT `True` …
#   `theorem foo (_ : ℝ) : ∀ (_ : ℂ), True := fun _ => trivial`  -- … and args come first
#
# The third and fourth shapes hid `thm_universal_shadow_product` and
# `scaling_eigenspace_ode` — both unprefixed — until 2026-09-01. The earlier version keyed
# on the binder being literally `True` and the proof being literally `trivial`; neither is
# what makes a declaration vacuous. What makes it vacuous is the conclusion.
STUB = re.compile(
    # (a) The original two shapes, kept verbatim. Widening this pattern must never *lose* a
    #     detection, and taking the union by construction is the only way to guarantee that
    #     -- an earlier attempt at a "cleaner" single pattern silently dropped four stubs
    #     written as `by intro _ <newline> trivial`, because it required a semicolon.
    r":\s*True\s*:=\s*(?:by\s+)?trivial\b"
    r"|∀\s*\(_\s*:\s*True\)\s*,\s*True\s*:="
    # (b) Conclusion `True` under ANY binders, with a trivial-equivalent proof. What makes a
    #     declaration vacuous is its conclusion -- not that the binder is literally `True`,
    #     and not that the proof is literally the token `trivial`. Keying on those was how
    #     `thm_universal_shadow_product` (`∀ (_ : ℂ), True := fun _ => trivial`) and
    #     `scaling_eigenspace_ode` (`(_ : ℝ) : ∀ (_ : ℂ), True := fun _ => trivial`) stayed
    #     invisible -- both unprefixed -- until 2026-09-01.
    r"|:\s*(?:∀[^,]*,\s*)*True\s*:=\s*(?:(?:by|fun|intro|=>|_|;)\s*)*trivial\b"
)

# The blueprint publishes this number in prose; keep it honest automatically.
BLUEPRINT = Path("blueprint/src/web.tex")
BLUEPRINT_COUNT = re.compile(r"There are currently \\textbf\{(\d+)\} such stubs\.")

# --------------------------------------------------------------------------------------
# Reflexivity tautologies -- a SECOND way to assert nothing (added 2026-09-01)
# --------------------------------------------------------------------------------------
#
# Everything above hunts for the conclusion `True`. That is not the only vacuous
# conclusion. A declaration whose conclusion is `X = X` for syntactically identical `X`
# is equally empty, is proved by `rfl`, and reports the same spotless axiom bill -- and
# because it is not `True`, every version of the gate so far walked straight past it.
#
# Eleven were in the tree when this check was written, none of them prefixed, several
# carrying the name of a substantive claim:
#
#   theorem three_generations : (3 : ℕ) = 3 := rfl            -- the headline SM prediction
#   lemma  test_function_fe_symmetric (h) (rho) : h rho = h rho := rfl
#   theorem mirror_baryon_lower_bound : (1 : ℕ) ≤ 1 := le_refl 1
#   theorem dim_sun (n) (_ : 1 ≤ n) : n^2 - 1 = n^2 - 1 := rfl
#   theorem kac_moody_level_appears_in_commutator (k m δ_ab δ_mn) : … = … := rfl
#
# `test_function_fe_symmetric` sat under a section header reading "algebraic spectral
# facts (proved clean)" and was `#check`ed in its file's summary. `three_generations`
# said "OPEN PROBLEM" in capitals in its own docstring.
#
# The check is deliberately syntactic and conservative: it compares the two sides of the
# top-level relation as text, after stripping one layer of type ascription, and only
# fires when they are character-for-character identical. `2 - (2 - Δ) = Δ` is not caught
# (nor should it be -- it is a real theorem); `2 - Δ = 2 - Δ` is.
RELATIONS = (" = ", " ↔ ", " ≤ ", " ⊆ ", " ⊇ ", " ≥ ")
ASCRIPTION = re.compile(r"^\((.*?)\s*:\s*[^:()]*\)$")


def _split_top(s: str, tok: str):
    """Split `s` at the first occurrence of `tok` at bracket depth 0."""
    depth = 0
    i = 0
    while i < len(s):
        c = s[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth == 0 and s.startswith(tok, i):
            return s[:i], s[i + len(tok):]
        i += 1
    return None, None


def _strip_ascription(x: str) -> str:
    x = x.strip()
    m = ASCRIPTION.match(x)
    return m.group(1).strip() if m else x


def is_reflexive_tautology(flat: str) -> bool:
    """True if the declaration's conclusion is `X R X` for identical `X`."""
    head, _ = _split_top(flat, " := ")
    if head is None:
        head, _ = _split_top(flat, ":= by")
    if head is None:
        return False
    _, stmt = _split_top(head, " : ")
    if stmt is None:
        return False
    stmt = stmt.strip()
    # Peel leading `∀ …,` binders so the conclusion is what gets compared.
    while stmt.startswith("∀"):
        _, rest = _split_top(stmt, ", ")
        if rest is None:
            break
        stmt = rest.strip()
    for tok in RELATIONS:
        lhs, rhs = _split_top(stmt, tok)
        if lhs is None:
            continue
        return bool(lhs) and _strip_ascription(lhs) == _strip_ascription(rhs)
    return False


def strip_comments(src: str) -> str:
    """Remove Lean line comments and (nested) block comments, preserving newlines.

    Newlines are preserved so that line numbers stay usable for error messages.
    """
    out: list[str] = []
    i = 0
    depth = 0
    n = len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if src.startswith("-/", i) and depth:
            depth -= 1
            i += 2
            continue
        if depth:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            if j < 0:
                break
            out.append(" " * (j - i))
            i = j
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def declarations(src: str):
    """Yield (name, line_number, flattened_text) for each theorem/lemma declaration."""
    starts = [m.start() for m in DECL_START.finditer(src)] + [len(src)]
    for a, b in zip(starts, starts[1:]):
        chunk = src[a:b]
        m = NAME.match(chunk)
        if not m:
            continue
        yield m.group(1), src.count("\n", 0, a) + 1, re.sub(r"\s+", " ", chunk).strip()


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    root = repo / "GppVerify"
    offenders: list[str] = []
    tautologies: list[str] = []
    total = 0

    for path in sorted(root.rglob("*.lean")):
        src = strip_comments(path.read_text())
        for name, lineno, flat in declarations(src):
            if STUB.search(flat):
                total += 1
                if not name.startswith("open_"):
                    offenders.append(f"{path.relative_to(repo)}:{lineno}: {name}")
                continue
            if is_reflexive_tautology(flat):
                tautologies.append(f"{path.relative_to(repo)}:{lineno}: {name}")

    print(f"True-stubs found: {total}")

    failed = False
    if offenders:
        failed = True
        print(f"::error::{len(offenders)} stub(s) do not use the required 'open_' prefix.")
        print("A `True := trivial` stub asserts nothing but reports a clean axiom bill.")
        print("Prefix the name with 'open_' so it cannot be mistaken for a proved result:")
        for entry in offenders:
            print(f"  {entry}")
    else:
        print("All True-stubs correctly prefixed 'open_'.")

    if tautologies:
        failed = True
        print(f"::error::{len(tautologies)} declaration(s) state `X = X` for identical X.")
        print("A reflexivity tautology asserts nothing, exactly like a `True` stub, but")
        print("carries a real-looking statement. Either state what the name claims, or")
        print("make it an honest `open_… : True := trivial` stub so it gets counted:")
        for entry in tautologies:
            print(f"  {entry}")
    else:
        print("No reflexivity tautologies (`X = X`) found.")

    # The blueprint states the stub count in prose. A hand-maintained number drifts --
    # it already had (141 published against 150 actual) -- so check it here rather than
    # trusting whoever edits the LaTeX next.
    blueprint = repo / BLUEPRINT
    if blueprint.exists():
        m = BLUEPRINT_COUNT.search(blueprint.read_text())
        if not m:
            failed = True
            print(
                "::error::Could not find the stub count sentence in "
                f"{BLUEPRINT}. Expected the exact phrasing "
                r"'There are currently \textbf{N} such stubs.'"
            )
        elif int(m.group(1)) != total:
            failed = True
            print(
                f"::error::{BLUEPRINT} states {m.group(1)} stubs; the tree has {total}. "
                "Update the blueprint sentence so the published ledger is not a lie."
            )
        else:
            print(f"Blueprint stub count agrees with the tree ({total}).")

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
