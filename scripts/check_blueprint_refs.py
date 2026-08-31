#!/usr/bin/env python3
"""Gate: every `\\lean{...}` in the blueprint must name a declaration that exists,
and no `\\label{...}` may be defined twice.

Why this exists
---------------
On 2026-08-31 an audit found **17 dangling `\\lean{}` references** in
`blueprint/src/web.tex` and **two duplicated labels**. Several of the dangling
references carried `\\leanok`, i.e. the published blueprint at
lean.goldenphysics.org asserted a result was machine-verified while pointing at an
identifier that no longer existed in the Lean tree. None of it was caught by CI,
because `build.yml` checks the Lean build and `blueprint.yml` only checks that
LaTeX compiles — neither cross-checks the two against each other.

Causes were mundane and will recur without a gate:
  * declarations renamed (the `open_` stub-prefix pass renamed ~143 of them),
  * a thread re-proved under a better route, leaving the old names behind,
  * two chapters independently claiming the same `\\label`.

This script is deliberately syntactic: it does not parse Lean, it greps for
declaration headers. That is enough to catch a name that is simply gone, which is
the failure mode that actually happened, and it costs no build time.

Exit status: 0 clean, 1 on any dangling reference or duplicate label.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
BLUEPRINT = REPO / "blueprint" / "src" / "web.tex"
LEAN_ROOT = REPO / "GppVerify"

# Every form that introduces a name we might point `\lean{}` at. `structure` and
# `instance` matter: an earlier version of this check omitted `structure` and
# produced a false positive on `GppTreeLoopSewing.ShadowPairSewing`.
DECL_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "axiom",
    "structure",
    "inductive",
    "instance",
    "class",
    "opaque",
)

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"           # optional attributes
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:" + "|".join(DECL_KEYWORDS) + r")\s+"
    r"(?P<name>[^\s({\[:]+)",
    re.MULTILINE,
)


def collect_declared_names() -> set[str]:
    names: set[str] = set()
    for path in LEAN_ROOT.rglob("*.lean"):
        for m in DECL_RE.finditer(path.read_text(encoding="utf-8")):
            # Strip a namespace prefix if the declaration was written dotted.
            names.add(m.group("name").split(".")[-1])
    return names


def main() -> int:
    if not BLUEPRINT.exists():
        print(f"blueprint not found at {BLUEPRINT}", file=sys.stderr)
        return 1

    text = BLUEPRINT.read_text(encoding="utf-8")
    declared = collect_declared_names()

    failures: list[str] = []

    # 1. Dangling \lean{} references.
    refs = re.findall(r"\\lean\{([^}]+)\}", text)
    dangling = []
    for ref in sorted(set(refs)):
        # `\lean{}` may name a dotted path; only the final component is the decl.
        base = ref.split(".")[-1].strip()
        if base not in declared:
            dangling.append(ref)
    if dangling:
        failures.append(
            "Dangling \\lean{} references (no such declaration in GppVerify/):\n"
            + "\n".join(f"    {r}" for r in dangling)
        )

    # 2. Duplicate \label{}.
    labels = re.findall(r"\\label\{([^}]+)\}", text)
    seen: set[str] = set()
    dupes: list[str] = []
    for lab in labels:
        if lab in seen and lab not in dupes:
            dupes.append(lab)
        seen.add(lab)
    if dupes:
        failures.append(
            "Duplicate \\label{} (LaTeX will cross-reference only one of each):\n"
            + "\n".join(f"    {d}" for d in dupes)
        )

    if failures:
        print("Blueprint reference check FAILED.\n")
        for f in failures:
            print(f + "\n")
        print(
            "Fix by repointing \\lean{} at the current declaration name, or by\n"
            "renaming the duplicated label. Do not delete a \\leanok to silence this."
        )
        return 1

    print(
        f"Blueprint reference check passed: "
        f"{len(set(refs))} \\lean{{}} refs all resolve, "
        f"{len(labels)} labels all unique."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
