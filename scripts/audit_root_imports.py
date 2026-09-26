#!/usr/bin/env python3
"""Audit GppVerify modules not reachable by a direct root/FullConstruction import.

This is intentionally a census, not a failing gate: some Thread/archive/experimental
modules can be intentionally unpromoted.  The output makes that distinction auditable
instead of allowing orphaned proof files to accumulate silently.
"""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "GppVerify"
ROOT_FILE = ROOT / "GppVerify.lean"
FULL = SRC / "FullConstruction.lean"

IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.'-]+)\s*$", re.M)

def imports(path: Path) -> set[str]:
    return set(IMPORT.findall(path.read_text(encoding="utf-8")))

def module_name(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)

all_modules = {
    module_name(p)
    for p in SRC.rglob("*.lean")
    if p.name != "FullConstruction.lean"
}
root_imports = imports(ROOT_FILE)
full_imports = imports(FULL)
covered_directly = root_imports | full_imports
missing = sorted(all_modules - covered_directly)

payload = {
    "lean_modules": len(all_modules),
    "root_direct_imports": len(root_imports),
    "fullconstruction_extra_imports": len(full_imports - root_imports),
    "not_directly_wired": len(missing),
    "modules": missing,
}
print(json.dumps(payload, indent=2))
