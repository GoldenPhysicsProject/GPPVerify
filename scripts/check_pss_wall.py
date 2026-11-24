#!/usr/bin/env python3
"""The PSS import wall: no file of the Pasterski–Shao(–Strominger) package may reach the
RiemannHypothesis tree, directly or transitively.

Spec: GPP-bridge MuseResearch/turbo-pss-inventory-spec-2026-11-13.md, §3 ("No physics file may
import anything from GppVerify/RiemannHypothesis/ — that import direction is the anti-smuggling
wall"). Nine older CelestialHolography files already import the RH tree, so a direct-import grep is
not enough: a PSS file importing one of them would breach the wall one step removed. This script
walks the import graph inside GppVerify and fails if any path from a package file reaches a
RiemannHypothesis module. The dictionary file (RiemannHypothesis/PasterskiShaoDictionary.lean) is
the one sanctioned crossing and is not a package file.

Package files are the modules listed in PACKAGE below that exist on disk. Mathlib and other
external imports are not followed (they cannot reach GppVerify).
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "GppVerify"

PACKAGE = [
    "GppVerify.CelestialHolography.ConformalPrimaryWavefunction",
    "GppVerify.CelestialHolography.KleinGordonPairing",
    "GppVerify.CelestialHolography.PSSRadialPairing",
    "GppVerify.CelestialHolography.PSSNormalizability",
    "GppVerify.CelestialHolography.PSSCompleteness",
    "GppVerify.CelestialHolography.PSSShadowTransform",
    "GppVerify.Analysis.MellinPlancherelHalfLine",
    "GppVerify.Analysis.MellinPlancherelL2",
]
FORBIDDEN = "GppVerify.RiemannHypothesis."
IMPORT = re.compile(r"^\s*(?:public\s+)?import\s+([\w.]+)", re.M)


def path_of(mod: str) -> pathlib.Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def imports(mod: str) -> list[str]:
    p = path_of(mod)
    if not p.exists():
        return []
    return [m for m in IMPORT.findall(p.read_text()) if m.startswith("GppVerify")]


def find_breach(start: str) -> list[str] | None:
    """Return an import chain from `start` to a forbidden module, or None."""
    parent: dict[str, str | None] = {start: None}
    stack = [start]
    while stack:
        mod = stack.pop()
        for nxt in imports(mod):
            if nxt in parent:
                continue
            parent[nxt] = mod
            if nxt.startswith(FORBIDDEN):
                chain = [nxt]
                cur: str | None = mod
                while cur is not None:
                    chain.append(cur)
                    cur = parent[cur]
                return list(reversed(chain))
            stack.append(nxt)
    return None


def main() -> int:
    present = [m for m in PACKAGE if path_of(m).exists()]
    bad = False
    for mod in present:
        chain = find_breach(mod)
        if chain:
            bad = True
            print(f"WALL BREACH: {' -> '.join(chain)}")
    if bad:
        print("\nA PSS package file reaches GppVerify/RiemannHypothesis/. Remove the import or move the"
              "\nneeded lemma to a neutral home (GppVerify/Analysis/). Only the dictionary may cross.")
        return 1
    print(f"PSS wall holds: {len(present)} package file(s), none reaches GppVerify.RiemannHypothesis.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
