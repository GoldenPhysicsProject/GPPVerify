# discovery/cutkosky_weil

Search-and-discovery sandbox for the 2026-08-22 research-front directive "celestial
Cutkosky positivity → local shadow kernels → finite-prime Weil kernel → Casimir
compression → global Weil positivity → RH" — same convention as
`discovery/local_field_shadow/` and `discovery/shadow_ope/`: **discovery only, except
where explicitly noted as formalized in Lean.**

- `notes.md` — the full write-up: the central research question (what projection turns
  `K_p` into `K_p−1` while preserving positivity) and its rigorously-computed answer,
  what's proved in Lean, what's numerical-only, and the honest boundary. Read this first.
- `cutkosky_weil_verify.py` — independent numerical verification of every identity
  discussed, rerun fresh in this container.
- Lean formalization lives in
  `GppVerify/RiemannHypothesis/CutkoskyWeilBridge.lean` (`Kp`, `Wp`, `cutKernel`, `H`,
  `Kp_pos`, `H_nonneg`).

**This is a new research front, not an RH proof, and not evidence toward RH.** See
`notes.md`'s "Explicit non-claims" section for the full list of things this work does
*not* establish. The central finding of this round is a *negative* result: no
positivity-preserving projection from `K_p` to `K_p − 1` exists at the single-prime
level (Toeplitz/Bochner indefiniteness, confirmed for p=2,3,5).
