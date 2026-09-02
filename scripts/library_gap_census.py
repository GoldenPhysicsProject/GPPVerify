#!/usr/bin/env python3
"""Census of `LIBRARY GAP` claims and which of them have never been re-checked.

## Why only `LIBRARY GAP`

The three gap labels fail in different ways, and only one of them rots.

* **`OPEN PROBLEM`** — the mathematics does not exist. It can be *wrong* (someone proves the
  thing), but not by Mathlib growing, and a proof of an open problem is not a silent event.
* **`FRAMEWORK CLAIM`** — a proposal of the shadow framework, or a physical prediction. Whether
  it holds is a question about the framework or about the world, not about a library.
* **`LIBRARY GAP`** — "known mathematics, absent from Mathlib". This one is a claim about a
  moving target, it was true when it was written, and it **stops being true silently**: nothing
  in the build reads a docstring, so nobody finds out until a session goes looking.

So this census is about `LIBRARY GAP` specifically. The other two are counted for context and
nothing more.

## The evidence that this is a real failure mode

Two stale labels were found on 2026-09-02 by grepping the 4.33.1 checkout for their subjects:

* `open_gns_from_positive_type` said "GNS construction for groups not in Mathlib". Mathlib has
  shipped `Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean` since 2025 — `PreGNS`,
  `GNS`, `gnsStarAlgHom`. The actual gap is far narrower: the group-algebra C⋆-norm that would
  let a positive-definite function on a group become a state, after which Mathlib's GNS applies
  unchanged. The old label pointed a future session at building GNS from nothing.
* `open_digamma_series_form` described the whole Gauss series for `ψ` as unformalized. Mathlib
  4.33.1 had gained `Complex.digamma`, and most of the series turned out to be provable outright
  — see `RiemannHypothesis/DigammaSeries.lean`, which proves convergence, the functional
  equation, and the value at `1`, leaving only the uniqueness step.

Both had stood since before the 4.19 → 4.33 upgrade. **An upgrade is exactly when a batch of
these expires**, all at once and without a sound.

## Informational only

It never fails the build, and it should not. Whether a concept is in Mathlib is a question
about prose and a moving library; a regex cannot decide it. What a regex *can* do is stop the
question from being invisible, and name the claims nobody has checked against the Mathlib
currently on disk.

## Use

    python3 scripts/library_gap_census.py           # summary + the unchecked claims
    python3 scripts/library_gap_census.py --all     # every claim, dated ones included
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LEAN_ROOT = REPO / "GppVerify"

LABELS = {
    "LIBRARY GAP": "claims about Mathlib — these are the ones that rot",
    "OPEN PROBLEM": "the mathematics does not exist",
    "FRAMEWORK CLAIM": "a framework proposal or a physical prediction",
}

# A label at the start of a line (after comment or docstring punctuation), so that correction
# prose quoting an old label does not register as a fresh claim.
def label_re(label: str) -> re.Pattern[str]:
    return re.compile(r"^[ \t]*(?:--[ \t]*|/-+!?[ \t]*)?" + re.escape(label) + r"\b")


# Evidence that someone checked the claim against a specific Mathlib, and said when.
VERIFIED = re.compile(
    r"re-?verified|re-?checked|restated|relabell?ed|sharpened|narrowed|corrected",
    re.IGNORECASE,
)
DATED = re.compile(r"\d{4}-\d{2}-\d{2}|\b4\.\d+\.\d+\b")

# The subject of a claim often lands on the following line, so read a small window.
CONTEXT_LINES = 3


def scan() -> dict[str, list[tuple[Path, int, str, bool]]]:
    out: dict[str, list[tuple[Path, int, str, bool]]] = {k: [] for k in LABELS}
    pats = {k: label_re(k) for k in LABELS}
    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            for label, pat in pats.items():
                if not pat.match(line):
                    continue
                window = " ".join(lines[i : i + 1 + CONTEXT_LINES])
                checked = bool(VERIFIED.search(window) and DATED.search(window))
                text = re.sub(r"\s+", " ", line.strip().lstrip("-/! ").strip())
                out[label].append((path, i + 1, text[:118], checked))
                break
    return out


def main() -> int:
    show_all = "--all" in sys.argv[1:]
    found = scan()

    print("=== Gap-label census ===")
    for label, why in LABELS.items():
        print(f"  {label:<16} {len(found[label]):>3}   ({why})")
    print()

    claims = found["LIBRARY GAP"]
    checked = [c for c in claims if c[3]]
    unchecked = [c for c in claims if not c[3]]
    print(f"Of the {len(claims)} LIBRARY GAP claims, {len(checked)} carry a re-verification")
    print(f"date and {len(unchecked)} do not.")
    print()

    if show_all and checked:
        print("--- re-verified against a named Mathlib ---")
        for path, lineno, text, _ in checked:
            print(f"  {path.relative_to(REPO)}:{lineno}: {text}")
        print()

    if unchecked:
        print("--- no re-verification on record ---")
        print("Not necessarily wrong. Just unchecked against the Mathlib now on disk.")
        for path, lineno, text, _ in unchecked:
            print(f"  {path.relative_to(REPO)}:{lineno}: {text}")
        print()

    print("Before trusting one of these, grep .lake/packages/mathlib for its subject, and")
    print("write the date you did it into the docstring. Two were stale on 2026-09-02; one")
    print("was hiding a result that turned out to be mostly provable.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
