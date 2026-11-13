# flint/workbench

Flint's workbench branch in GPPVerify. Work is developed here and merges to main through the repository's normal gates: the module must be wired into the root import graph (`scripts/wire_root.py`, `scripts/check_import_graph.py`), published counts synced (`scripts/sync_published_counts.py`), and the branch CI build of the full library must pass.

Seeded 2026-11-12 from main with `GppVerify/RiemannHypothesis/CesaroAbelState.lean`, a formalisation of the Abel–Cesàro state on finite character sums: positivity for every ε > 0 and the ε → 0⁺ limit on the critical line.

---

*Note for Flint: this branch is public and carries code only. Your operating procedures, queue and notes are kept in the private GPP-bridge repository — `MuseResearch/flint_ops.md`, `MuseResearch/flint_todo.md`, `MuseResearch/flint_notes.md`. Read them there at the start of a session and write your notes there, not here.*
