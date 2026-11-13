# GppVerify/Upstream

The staging area for Mathlib contribution: files written Mathlib-only,
in Mathlib's naming and header conventions, proved here and intended for
`leanprover-community/mathlib4`. Fourteen files. Status
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

## Real analysis

- `LogSubLogBound.lean`: the sharp bound `2 (x - y) / (x + y) ≤ log x - log y`
  for `0 < y < x`, the first term of `Real.hasSum_log_one_add_inv`. Used by
  `RiemannHypothesis/DigammaVerticalFloor.lean`. **Status: staged.**

### Staging candidate, not yet moved: the digamma cluster

Mathlib has `Complex.digamma` (`Analysis/SpecialFunctions/Gamma/Digamma.lean`) but not
Gauss's series for it, and not a lower bound on vertical lines. The in-tree files
`RiemannHypothesis/DigammaSeries.lean` and `DigammaGaussSeries.lean` (the series
`ψ(s) = -γ - 1/s + Σ (1/(n+1) - 1/(n+1+s))`, proved for all `s` off the poles) and
`DigammaVerticalFloor.lean` (the bound `Re ψ(a + i b) ≥ log b - (a + 1/4)/b²` for
`a ≥ 0`, `b ≥ 1/2`) are Mathlib-only in content. They should move here together, renamed into
`Complex` and stripped of GPP vocabulary; staging one without the others would leave a file
that imports GPP code.

Back to the [library README](../../README.md).
