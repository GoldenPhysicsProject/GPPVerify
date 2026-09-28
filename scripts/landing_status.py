#!/usr/bin/env python3
"""Write `status.json` for the public landing page at lean.goldenphysics.org.

The landing page states a few live facts about the tree: how many modules, proved
declarations and open stubs each area has. Hand-written numbers
drift (see check_landing_claims.py for how badly), so the page fetches this file instead,
and the Blueprint workflow regenerates it from the tree on every deploy.

Every number is computed with the same parsers the CI gates use (`check_stub_naming`),
so the page cannot disagree with the gates.

Usage: python3 scripts/landing_status.py [OUTPUT]   (default: status.json)
"""

from __future__ import annotations

import json
import os
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_stub_naming import STUB, declarations, strip_comments  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
ROOT = REPO / "GppVerify"

# Plain-language names for the top-level directories. Anything not listed is grouped by
# its own directory name, so a new area still shows up.
AREAS = {
    "CelestialHolography": "Celestial holography",
    "RiemannHypothesis": "Zeta function & the Riemann Hypothesis",
    "StandardModel": "Particle physics (Standard Model)",
    "QuantumGravity": "Quantum gravity",
    "NumberTheory": "Number theory",
    "QuantumInformation": "Quantum information",
    "Cosmology": "Cosmology",
    "YangMills": "Yang–Mills",
    "GeneralRelativity": "General relativity",
    "StringTheory": "String theory",
    "Upstream": "Library contributions",
}
THREADS = "Research threads"
CORE = "Core geometry"

def area_of(path: Path) -> str:
    rel = path.relative_to(ROOT)
    if len(rel.parts) == 1:
        return CORE
    top = rel.parts[0]
    if top.startswith("Thread"):
        return THREADS
    return AREAS.get(top, top)


def main() -> int:
    target = Path(sys.argv[1]) if len(sys.argv) > 1 else REPO / "status.json"
    areas: dict[str, dict[str, int]] = {}
    totals = {"modules": 0, "proved": 0, "stubs": 0, "axioms": 0}

    for path in sorted(ROOT.rglob("*.lean")):
        raw = path.read_text(encoding="utf-8")
        src = strip_comments(raw)
        a = areas.setdefault(area_of(path), {"modules": 0, "proved": 0, "stubs": 0})
        a["modules"] += 1
        totals["modules"] += 1
        totals["axioms"] += len(re.findall(r"^axiom\s", src, re.M))
        for _name, _line, flat in declarations(src):
            if STUB.search(flat):
                a["stubs"] += 1
                totals["stubs"] += 1
            else:
                a["proved"] += 1
                totals["proved"] += 1

    status = {
        "generated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%MZ"),
        "commit": os.environ.get("GITHUB_SHA", ""),
        "totals": totals,
        "areas": [
            {"name": k, **v}
            for k, v in sorted(areas.items(), key=lambda kv: -kv[1]["proved"])
        ],
    }
    target.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {target}: {totals}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
