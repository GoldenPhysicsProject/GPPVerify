# flint/workbench — Flint's standing workbench in GPPVerify

**Owner:** Flint (Discovery 3 seat, Muse Spark, under Turbo's direction).
**Purpose:** Flint's home branch. Work is built here; the branch CI's lake **Build** check (read the check NAME) is the compile receipt of record. Local compiles on the VM time out and prove nothing. When a file is green here and has passed firsthand audit by the paired seat, it merges from this branch.

## Gate suite (in order, before any "green" claim)

1. `python3 scripts/wire_root.py`
2. `python3 scripts/check_import_graph.py` — every module imported
3. `python3 scripts/sync_published_counts.py` — commit its changes
4. CI `lake build GppVerify` on this branch (workflow_dispatch) — the receipt
5. sorry/axiom audit of new files (`#print axioms`, standard three only: propext, Classical.choice, Quot.sound)

Module green is not tree green. Corrections are appended, never rewritten, each with a "Catch it next time" line.

## Seeded

2026-11-12, from main tip 5b97fa9, at Daniel's direction ("every bot should have their own workbench in Verify"), modelled on heart/workbench and claude/workbench, with this manifest added so any fresh Flint instance reconstitutes from the branch alone.

Seed content: `GppVerify/RiemannHypothesis/CesaroAbelState.lean` — the Abel–Cesàro state ω_ε on finite character sums, positivity for every ε, and the ε→0⁺ limit on the critical line (392 lines, 0 sorry at seeding). Flint's GNS completion (CesaroGNS.lean) joins this branch when its remaining obligations close.

## Queue (2026-11-12, takeover from Heart of the Cosmos)

1. Cesàro-GNS recovery: finish CesaroGNS.lean; named Prop `WeilIsGram` with `WeilIsGram → HPsi` proved; WeilIsGram itself not attempted yet.
2. Audit copies of Heart's banked branches (heart/workbench, heart/archpd stay untouched; audit and merge from flint copies).
3. ArchPosDef, then SemilocalArchDomAll, then WeilIsGram via the Connes semilocal route.
4. KreinDecomp: HELD. Do not attempt, widen, or restate until the Krein–Langer 1977 primary text is in hand.

H_ψ, ARP, RH: OPEN.
