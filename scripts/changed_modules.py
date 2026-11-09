#!/usr/bin/env python3
"""Print the Lean modules a branch changed, plus their dependents, one per line.

Used by the fast lane (`.github/workflows/claude-code-fast.yml`) to rebuild only what a
push can have affected, so the prove-fix-prove loop does not pay for a full clean build.
The full clean `Build` workflow stays the merge gate.

`python3 scripts/changed_modules.py <base-ref>` compares HEAD against `<base-ref>`, takes
every changed `GppVerify/**/*.lean`, and adds every module that imports one of them,
transitively. The root `GppVerify` is excluded: it imports everything, so it would turn
every run into the full build (the import-graph gate checks the root separately).
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = "GppVerify"
IMPORT = re.compile(r"^import\s+(GppVerify[\w.]*)", re.M)


def module_of(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)


def main() -> int:
    base = sys.argv[1]
    out = subprocess.run(
        ["git", "diff", "--name-only", "--diff-filter=AM", f"{base}...HEAD", "--", "GppVerify/**/*.lean"],
        check=True, capture_output=True, text=True).stdout.split()
    changed = {module_of(Path(f)) for f in out if Path(f).is_file()}
    changed.discard(ROOT)
    if not changed:
        return 0
    imports: dict[str, set[str]] = {}
    for f in Path("GppVerify").rglob("*.lean"):
        imports[module_of(f)] = set(IMPORT.findall(f.read_text(encoding="utf-8")))
    result = set(changed)
    grew = True
    while grew:
        grew = False
        for mod, deps in imports.items():
            if mod != ROOT and mod not in result and deps & result:
                result.add(mod)
                grew = True
    print("\n".join(sorted(result)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
