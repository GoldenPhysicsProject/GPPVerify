# GppVerify/Upstream

The staging area for Mathlib contribution: files written Mathlib-only,
in Mathlib's naming and header conventions, proved here and intended for
`leanprover-community/mathlib4`. Twenty-two files. Status
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

- `QuadraticFormLDL.lean`: a quadratic form is bounded below by `δ Σ x_i²` whenever
  `M = δ I + L D Lᵀ` entrywise with `D ≥ 0`, with a rational version
  (`Matrix.le_quadForm_of_ldl_rat`). This is the positive-definiteness step of a computer-assisted
  lower bound: the identity is checked by evaluation, the implication is proved once.
  **Status: staged.**

- `TwoVectorProjection.lean`: the orthogonal projection onto the span of
  two vectors, evaluated by Cramer's rule for the Gram matrix, and the
  squared distance formula. **Status: open as
  [mathlib4 PR #45825](https://github.com/leanprover-community/mathlib4/pull/45825)**,
  in adapted form at `Mathlib/Analysis/InnerProductSpace/Projection/SpanPair.lean`.

## Real analysis

- `LogSubLogBound.lean`: the sharp bound `2 (x - y) / (x + y) ≤ log x - log y`
  for `0 < y < x`, the first term of `Real.hasSum_log_one_add_inv`. Used by
  `RiemannHypothesis/DigammaVerticalFloor.lean`. **Status: staged.**
- `LogArctanBounds.lean`: two-sided rational enclosures of `log x` (`1 ≤ x`, via
  `u = (x-1)/(x+1)`: partial sums below, partial sum plus geometric tail above) and of
  `arctan x` (`0 ≤ x < 1`, alternating partial sums), written so `norm_num
  [Finset.sum_range_succ]` certifies ten-digit facts such as `log 2`, `log 3` and
  `arctan (1/2)` in seconds. The rational-arithmetic base for certificates. **Status: staged.**

- `DigammaGaussSeries.lean`: Gauss's series for the digamma function and a lower bound on
  vertical lines. `Complex.hasSum_digamma` / `Complex.digamma_eq_tsum`:
  `ψ(s) = -γ - 1/s + Σ_{n ≥ 0} (1/(n+1) - 1/(n+1+s))` for `s ∉ {0, -1, -2, …}` (Mathlib's
  `Analysis/SpecialFunctions/Gamma/Digamma.lean` lists this under `TODO`).
  `Real.tendsto_log_add_sub_sum_inv`: Gauss's limit on the positive reals, from the convexity of
  `log ∘ Γ`. `Complex.log_sub_le_re_digamma`: `log b - (a + 1/4)/b² ≤ Re ψ(a + b i)` for
  `0 ≤ a`, `1/2 ≤ b`. Self-contained, imports Mathlib and `LogSubLogBound.lean` only. It is a
  Mathlib-ready copy of `RiemannHypothesis/DigammaSeries.lean`, `DigammaGaussLimit.lean`,
  `DigammaGaussSeries.lean` and `DigammaVerticalFloor.lean`, which stay in place because other
  modules import them. **Status: staged.**

Back to the [library README](../../README.md).
