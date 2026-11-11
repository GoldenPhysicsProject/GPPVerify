# GppVerify/Upstream

The staging area for Mathlib contribution: files written Mathlib-only,
in Mathlib's naming and header conventions, proved here and intended for
`leanprover-community/mathlib4`. Thirteen files. Status
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

- `BoseIntegral.lean`: `d/dx log(1 - e^{-x}) = 1/(e^x - 1)`, the improper
  integral `∫_{(a,∞)} 1/(e^x - 1) dx = -log(1 - e^{-a})` for `a > 0` (with
  integrability), the fifth-order Taylor lower bound for `exp` on `[0, ∞)`,
  and the truncated Bernoulli bound `x/(e^x - 1) ≤ 1 - x/2 + x²/12`. Used by
  `NumberTheory/MestreRankKernel.lean` for the archimedean term of the
  elliptic explicit formula. Candidate homes: `Mathlib/Analysis/SpecialFunctions/
  Exponential*` and `.../ImproperIntegrals.lean`. **Status: staged.**

Back to the [library README](../../README.md).
