# discovery/cutkosky_weil

Search-and-discovery sandbox for the 2026-08-22 research-front directive "celestial
Cutkosky positivity → local shadow kernels → finite-prime Weil kernel → Casimir
compression → global Weil positivity → RH" — same convention as
`discovery/local_field_shadow/` and `discovery/shadow_ope/`: **discovery only, except
where explicitly noted as formalized in Lean.**

- `notes.md` — the full write-up: the central research question (what projection turns
  `K_p` into `K_p−1` while preserving positivity), a **self-correction** of this round's
  first-pass answer (read that section first), the corrected rigorous answer, what's
  proved in Lean, what's numerical-only, and the honest boundary.
- `cutkosky_weil_verify.py` — independent numerical verification of every identity
  discussed, rerun fresh in this container, including the corrected central experiment.
- Lean formalization lives in
  `GppVerify/RiemannHypothesis/CutkoskyWeilBridge.lean` (`Kp`, `Wp`, `cutKernel`, `H`,
  `Kp_pos`, `H_nonneg`, `KrClosed`, and the layered finite Fourier/Gram-square development
  `gram_square_freq` → `gram_square_freqSum` → `gram_square_freqSum_nonneg` →
  `KrN0`/`KrN0_gram_nonneg`). `notes.md`'s "Proof engineering" section explains why the
  layering — each piece under 4s to elaborate standalone — replaced an earlier monolithic
  attempt that hit elaboration timeouts even at 20× the default heartbeat budget.
- The Euler-factor and prime-power continuation lives in
  `GppVerify/RiemannHypothesis/EulerFactorLogDeriv.lean`: the genuine derivative identity,
  the exact equality `Wp = 2 Re(-ζ'_p/ζ_p)`, the absolutely summable two-sided expansion
  with coefficients `log(p) p^{-|n|/2}`, and a proof that the conventionally signed scalar
  multiplier `-Wp` takes both signs.
- `PrimeGreenAmplitude.lean` identifies those same coefficients and frequencies with the
  positive prime-power boundary atoms and proves the exact finite massive-resolvent sum.
  `PrimeFermionDirac.lean` realizes one Euler holonomy as a genuine two-state CAR/Koszul
  Hodge--Dirac system with strictly positive local critical-line energy.
- `NumberTheory/TwinPrimeDoublets.lean` records a separate two-prime correlation fact:
  above `5`, the gap-2 prime graph consists only of singlets and disjoint doublets, while
  `3-5-7` is the unique overlapping triplet.

**This is a new research front, not an RH proof, and not evidence toward RH.** See
`notes.md`'s "Explicit non-claims" section for the full list of things this work does
*not* establish. The corrected central finding: `K_p − 1` **is** positive-definite as a
kernel, prime-by-prime — trivially, since convolution by `K_p` is diagonal in the
Fourier basis with nonnegative eigenvalues, and the vacuum subtraction only zeroes the
`n=0` eigenvalue. This does not by itself bridge to global Weil positivity (still open —
see `notes.md`). In particular, positive convolution and pointwise multiplication are
different operators; `-Wp` is not sign-definite.
