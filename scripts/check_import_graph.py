#!/usr/bin/env python3
"""Fail the build if any module under `GppVerify/` is missing from `GppVerify.lean`.

## Why this exists — credit to Codex, 2026-09-01

`lake build GppVerify` builds the root module and everything it transitively imports.
A `.lean` file that sits in the tree but is absent from `GppVerify.lean`'s import list is
**never compiled at all**. It can fail to build, contain a `sorry`, or declare an axiom, and
the root build reports success without ever having looked at it.

Codex hit this while porting Verify2 mathematics into the shared tree: its root build passed
while a newly added module was broken, and it fixed the hole on its side by having CI compile
every changed `GppVerify/**/*.lean` explicitly. It wrote that up in
`gpp-bridge/CODEX_RESEARCH_NOTES.md`, which is how this side found out.

Checking here immediately: **15 of 185 modules were outside the root import graph** — the
`RiemannHypothesis/` group listed below at the time of writing. So PR #133's claim that "the
whole tree builds clean" under Mathlib 4.33.1 had never been tested against them. They were
each built explicitly and all passed, so nothing was actually broken; but the gate genuinely
was not covering them, and "nothing was broken this time" is not a gate.

This is the same shape as the cached-`sorry` hole (`check_sorries.py`): a check that reads
what the *build* happened to look at, rather than what the *tree* contains. Two different
mechanisms, one lesson — **tree-wide invariants must be checked against the tree.**

## What this checks

Every `GppVerify/**/*.lean` appears as an `import` in `GppVerify.lean`. That makes the root
build cover the whole tree, which in turn makes the build-log `sorry` gate, the axiom audit,
and the compile check itself meaningful repo-wide rather than merely graph-wide.

If a module is deliberately excluded — a scratch file, a deprecated module kept for
reference — add it to `INTENTIONALLY_UNIMPORTED` below with a reason. An explicit, reviewed
exclusion is fine; an accidental one is the bug.
"""

import re
import sys
from pathlib import Path

ROOT_MODULE = "GppVerify.lean"
PACKAGE_DIR = "GppVerify"

# Modules deliberately kept out of the root import graph, each with a stated reason.
# Empty by design: every exclusion should be argued for in review, not inherited silently.
INTENTIONALLY_UNIMPORTED: dict[str, str] = {}

IMPORT_RE = re.compile(r"^import\s+(GppVerify(?:\.[A-Za-z0-9_']+)*)\s*$", re.M)


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    root = repo / ROOT_MODULE
    if not root.exists():
        print(f"::error::{ROOT_MODULE} not found", file=sys.stderr)
        return 1

    imported = set(IMPORT_RE.findall(root.read_text(encoding="utf-8")))

    on_disk: dict[str, Path] = {}
    for path in sorted((repo / PACKAGE_DIR).rglob("*.lean")):
        rel = path.relative_to(repo).with_suffix("")
        on_disk[".".join(rel.parts)] = path

    missing = [m for m in sorted(on_disk) if m not in imported
               and m not in INTENTIONALLY_UNIMPORTED]

    # An import naming a module that no longer exists breaks the build outright, but name it
    # clearly rather than leaving it to a Lean error.
    stale = [m for m in sorted(imported) if m not in on_disk]

    print(f"Modules on disk: {len(on_disk)}   imported by {ROOT_MODULE}: {len(imported)}")

    failed = False
    if missing:
        failed = True
        print(f"::error::{len(missing)} module(s) are not imported by {ROOT_MODULE}, so")
        print("`lake build GppVerify` never compiles them. They can be broken, carry a")
        print("`sorry`, or declare an axiom while CI reports the tree green. Add each to")
        print(f"{ROOT_MODULE}, or list it in INTENTIONALLY_UNIMPORTED with a reason:")
        for m in missing:
            print(f"  {m}")

    if stale:
        failed = True
        print(f"::error::{len(stale)} import(s) in {ROOT_MODULE} name a module that does "
              "not exist on disk:")
        for m in stale:
            print(f"  {m}")

    if not failed:
        print(f"Every module under {PACKAGE_DIR}/ is in the root import graph.")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
