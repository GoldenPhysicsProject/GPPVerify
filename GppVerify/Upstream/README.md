# GppVerify/Upstream

The staging area for Mathlib contribution: files written Mathlib-only,
in Mathlib's naming and header conventions, proved here and intended for
`leanprover-community/mathlib4`. 23 files. Status
is recorded per file; at the time of writing one pull request is open
and the rest are staged, none merged yet.

## The entire-function cluster

Hadamard theory Mathlib does not have: the order of growth of an entire
function and its consequences.

- `OrderOfGrowth.lean`: order of growth of an entire function.
- `ZeroCounting.lean`: the zero-counting bound for finite order.
- `ZeroSummability.lean`: the zeros are summable beyond the order.
- `DyadicSummability.lean`: summability from a polynomial counting bound.
- `WeierstrassFactor.lean`: the elementary factors.
- `WeierstrassProduct.lean`: the product theorem.

## The adele files

From the Tate layer ([`../../docs/TATE-GUIDE.md`](../../docs/TATE-GUIDE.md)),
written against Mathlib's own adele API:

- `RatAdeleRingEquiv.lean`: Mathlib's `AdeleRing ℤ ℚ` is `ℝ × 𝔸_f`, as a
  ring equivalence and a homeomorphism, with the diagonal law.
- `RatFiniteAdeleRingHaar.lean`: Haar measure on the finite adeles of ℚ,
  with `vol(∏_p ℤ_p) = 1` under the normalization.
- `RatFiniteAdeleRingApprox.lean`: strong approximation for the finite
  adeles of ℚ, upstream-style.
- `RatFiniteAdeleRingLattice.lean`: the lattices `N·∏ℤ_v` and their Haar
  volumes.
- `RatFiniteAdeleRingNhds.lean`: the lattices `N·∏ℤ_v` are a neighbourhood
  basis of `0`.
- `RatFiniteAdeleRingSchwartzBruhat.lean`: locally constant, compactly
  supported functions are uniformly locally constant and finite combinations
  of coset indicators.

Staging constraint for the three files that use `Rat.HeightOneSpectrum.primesEquiv`
(`Haar`, `Approx`, `Nhds`): avoid simp-family tactics (`simp`, `simpa`, `norm_cast`,
`push_cast`, `exact_mod_cast`) on goals containing `primesEquiv v`. Such a call makes Lean
realize the generated congruence lemma `primesEquiv.congr_simp`, whose statement is
literally `primesEquiv = primesEquiv` because every argument is instance-implicit. It is
then stored in whichever GppVerify module first needs it, and the native stub audit
(`scripts/check_native_stubs.lean`) correctly rejects it as an `a = a` theorem. Direct
lemma applications (`Nat.one_lt_cast.mpr`, `Rat.cast_le`, explicit `rw`) avoid it, and
they are equally acceptable upstream.

## Linear algebra

- `TwoVectorProjection.lean`: the orthogonal projection onto the span of
  two vectors, evaluated by Cramer's rule for the Gram matrix, and the
  squared distance formula. **Status: open as
  [mathlib4 PR #45825](https://github.com/leanprover-community/mathlib4/pull/45825)**,
  in adapted form at `Mathlib/Analysis/InnerProductSpace/Projection/SpanPair.lean`.

## Real analysis and explicit-formula numerics

Used by `NumberTheory/MestreRankKernel.lean`, the kernel-proved Mestre rank bounds for 11a1 and
37a1. None of these files imports GppVerify. Before upstreaming, search mathlib4 for overlap
(rule 3); none was found at the current pin.

- `BoseIntegral.lean`:
  - `Real.hasDerivAt_log_one_sub_exp_neg`;
  - the improper integral `Real.integral_Ioi_one_div_exp_sub_one`:
    `∫_{(a,∞)} 1/(e^x - 1) = -log(1 - e^{-a})`, with integrability;
  - `Real.quintic_le_exp_of_nonneg` (Taylor lower bound);
  - the truncated Bernoulli bound `Real.div_exp_sub_one_le`: `x/(e^x-1) ≤ 1 - x/2 + x²/12`,
    and `Real.div_exp_sub_one_le_one`;
  - `Real.integrableOn_Ioc_div_exp_sub_one`;
  - `Real.setIntegral_Ioc_div_exp_sub_one_le`: `∫_{(0,b]} x/(e^x-1) ≤ b - b²/4 + b³/36`.

  Candidate homes: `Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean` and
  `.../Exponential*`. **Status: staged.**
- `TriangleFunction.lean`: the Fejér triangle `max (a - |x|) 0`. It is continuous, vanishes for
  `a ≤ |x|`, and has `Real.integral_max_sub_abs : ∫ max (a - |x|) 0 = a²`. Candidate home:
  `Mathlib/MeasureTheory/Integral/...` next to `integral_comp_abs`. **Status: staged.**
- `LogPiBounds.lean`: `Real.log_pi_gt_d2 : 1.14 < log π` and `Real.log_pi_lt_d2 : log π < 1.15`.
  These are companions to `Real.log_two_gt_d9` and `Real.log_three_gt_d9` in
  `Mathlib/Analysis/Complex/ExponentialBounds.lean`. **Status: staged.**

## Elliptic curves

- `WeierstrassAffinePointCount.lean`: `WeierstrassCurve.Affine.numAffinePoints`, the number of
  affine points as a `Nat.card`. `numAffinePoints_eq_card_filter` gives it as an explicit
  `Finset.filter` card over a finite ring, so small cases close by `decide`. Candidate home:
  `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/`, as a first step toward `#E(𝔽_q)` and `a_p`.
  **Status: staged.**

Back to the [library README](../../README.md).
