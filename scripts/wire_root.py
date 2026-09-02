#!/usr/bin/env python3
"""Add any `GppVerify/**/*.lean` missing from `GppVerify.lean` to the root import graph.

## Why this exists

`check_import_graph.py` *detects* modules outside the root import graph — a real hole, since
`lake build GppVerify` never compiles them, so they can be broken, carry a `sorry`, or declare
an axiom while CI reports green. This script *fixes* what that gate detects.

It exists because detection alone created a recurring two-agent handoff. Codex adds modules on
a payload branch; the gate correctly rejects the branch; Codex cannot add the imports itself,
because its connector can only replace a file wholesale and `GppVerify.lean` is ~86 KB of
hand-curated section comments that a wholesale rewrite would destroy. Every such branch then
waited on a manual wiring pass from the other side. That is a tooling problem wearing the
costume of a coordination problem, and it should not consume a round trip each time.

## Why it appends rather than regenerates

The obvious implementation — rebuild the file from the modules on disk — is wrong. The root
module is not only imports: it carries the section headers and per-import commentary that
explain the tree's structure ("RH Pathway 2: Spectral / Meyer", notes on which axioms were
retired and when). Regenerating would silently delete all of it. So this script only ever
*adds* lines, under one clearly marked section, and never rewrites or reorders what is
already there. Nothing you wrote by hand can be lost by running it.

Moving an import out of the auto-wired block into a curated section, with a comment saying
what the module is for, is an improvement — do it freely. The block is a staging area, not a
destination.

## Use

    python3 scripts/wire_root.py            # add missing imports
    python3 scripts/wire_root.py --check    # report only, exit 1 if any are missing

Idempotent: a second run is a no-op. Stale imports (naming a module that does not exist) are
reported but never removed automatically — deleting an import can break a build in a way
adding one cannot, so that stays a human decision.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT_MODULE = "GppVerify.lean"
PACKAGE_DIR = "GppVerify"
IMPORT_RE = re.compile(r"^import\s+(GppVerify(?:\.[A-Za-z0-9_']+)*)\s*$", re.M)

MARKER = "-- ── Wired automatically by scripts/wire_root.py ─────────────"
MARKER_NOTE = (
    "-- Modules added here were on disk but outside the root import graph, so\n"
    "-- `lake build GppVerify` was not compiling them. Move an import up into the\n"
    "-- appropriate curated section above, with a note on what it is for, whenever\n"
    "-- you know where it belongs — this block is a staging area, not a destination.\n"
)


def main() -> int:
    check_only = "--check" in sys.argv[1:]
    repo = Path(__file__).resolve().parent.parent
    root = repo / ROOT_MODULE
    if not root.exists():
        print(f"{ROOT_MODULE} not found", file=sys.stderr)
        return 1

    text = root.read_text(encoding="utf-8")
    imported = set(IMPORT_RE.findall(text))

    on_disk: dict[str, Path] = {}
    for path in sorted((repo / PACKAGE_DIR).rglob("*.lean")):
        rel = path.relative_to(repo).with_suffix("")
        on_disk[".".join(rel.parts)] = path

    missing = sorted(m for m in on_disk if m not in imported)
    stale = sorted(m for m in imported if m not in on_disk)

    if stale:
        print(f"note: {len(stale)} import(s) name a module that is not on disk. These are")
        print("NOT removed automatically — deleting an import can break a build in a way")
        print("adding one cannot. Check whether the file was renamed or deleted:")
        for m in stale:
            print(f"  {m}")

    if not missing:
        print(f"Root import graph is complete ({len(on_disk)} modules).")
        return 0

    print(f"{len(missing)} module(s) missing from {ROOT_MODULE}:")
    for m in missing:
        print(f"  {m}")

    if check_only:
        print("\n--check given; nothing written. Run without it to wire them in.")
        return 1

    block = "\n".join(f"import {m}" for m in missing) + "\n"
    if MARKER in text:
        # Extend the existing block rather than starting a second one.
        head, tail = text.split(MARKER, 1)
        lines = tail.splitlines(keepends=True)
        i = 0
        while i < len(lines) and (lines[i].startswith("--") or lines[i].startswith("import")
                                  or not lines[i].strip()):
            i += 1
        text = head + MARKER + "".join(lines[:i]).rstrip("\n") + "\n" + block + "".join(lines[i:])
    else:
        text = text.rstrip("\n") + "\n\n" + MARKER + "\n" + MARKER_NOTE + block

    root.write_text(text, encoding="utf-8")
    print(f"\nWired {len(missing)} import(s) into {ROOT_MODULE}.")
    print("Build before committing: adding an import to the root graph is exactly the point")
    print("at which a module that never compiled starts having to.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
