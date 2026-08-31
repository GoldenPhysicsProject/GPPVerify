#!/usr/bin/env python3
"""Enforce the open_-prefix convention on `True`-stubs.

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

Exit 1 (failing the build) if any `True`-stub declaration lacks the prefix.
"""

import re
import sys
from pathlib import Path

DECL = re.compile(r"^\s*(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)")
STUB = re.compile(r":\s*True\s*:=\s*trivial|∀\s*\(_\s*:\s*True\),\s*True")

def main() -> int:
    root = Path(__file__).resolve().parent.parent / "GppVerify"
    offenders: list[str] = []
    total = 0

    for path in sorted(root.rglob("*.lean")):
        current: tuple[str, int] | None = None
        for lineno, line in enumerate(path.read_text().splitlines(), start=1):
            decl = DECL.match(line)
            if decl:
                current = (decl.group(1), lineno)
            if current and STUB.search(line):
                name, declared_at = current
                total += 1
                if not name.startswith("open_"):
                    offenders.append(f"{path}:{declared_at}: {name}")
                current = None

    print(f"True-stubs found: {total}")
    if offenders:
        print(f"::error::{len(offenders)} stub(s) do not use the required 'open_' prefix.")
        print("A `True := trivial` stub asserts nothing but reports a clean axiom bill.")
        print("Prefix the name with 'open_' so it cannot be mistaken for a proved result:")
        for entry in offenders:
            print(f"  {entry}")
        return 1

    print("All True-stubs correctly prefixed 'open_'.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
