# discovery/local_field_shadow

Search-and-discovery sandbox for "Local-field shadow kernels, celestial unitarity, and the
adelic principal series" (Toupin, 2026) — same convention as `discovery/shadow_ope/` and
[`weil-decay`](https://github.com/GoldenPhysicsProject/weil-decay): **discovery only, except
where explicitly noted as formalized in Lean.**

- `local_shadow_kernel_notes.md` — the full write-up: what's proved (in Lean), what's
  verified numerically only, and what's a genuinely open research problem. Read this first.
- `local_shadow_kernel_verify.py` — independent numerical verification of every identity in
  the paper, rerun fresh in this container (not copied from the source material).
- Lean formalization lives in `GppVerify/QuantumGravity/{LocalShadowKernel,
  DiagonalConformalLift,GlobalEisensteinCoefficient}.lean` (see `GppVerify.lean`'s import
  comments for what's covered).
- `golden_hyperbolic_verify.py` — supplementary numerical cross-check for
  `GppVerify/NumberTheory/GoldenRatioHyperbolicSector.lean` (the golden ratio as the
  minimal-trace hyperbolic element of `SL₂(ℤ)`, connected to the finite-place kernel
  `K_{5,1}(1/2)=φ²`). The Lean proofs are primary; this is a cross-check, not a substitute.

**This is a new research front, not an RH proof, and not evidence toward RH.** See
`local_shadow_kernel_notes.md`'s "Explicit non-claims" section for the full list of things
this work does *not* establish.
