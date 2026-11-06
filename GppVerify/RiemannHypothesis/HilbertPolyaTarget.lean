import GppVerify.RiemannHypothesis.ConditionalWeightStateLine
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic

/-!
# The Hilbert-Polya target: what "the zeros are the physical spectrum" must mean

The physical dilation generator `D = x d/dx + 1/2` of the massless sector has
purely continuous spectrum on `L^2` (Mellin-Plancherel, `GppMellinPlancherel`),
so the zeros of xi cannot be eigenvalues of `D` on the whole space. The
precise form of "the arithmetic s and the physical Delta are the same, zeros
included" is a Hilbert-Polya realization: a symmetric operator `T` on a
complex inner product space (for an unbounded operator, take the space to be
its domain with the restricted inner product) such that every zero `rho` of a
function `F` gives an eigenvalue `lambda` of `T` with `rho = 1/2 + i lambda`.

* `HilbertPolyaRealization F` packages that data for an arbitrary `F : ℂ → ℂ`.
* `re_eq_half_of_realization` proves (with no hypothesis beyond the data) that
  a realization puts every zero of `F` on `Re s = 1/2`: eigenvalues of a
  symmetric operator are real.
* `no_realization_of_off_line_zero` is the contrapositive. For any `F` with a
  zero off the line (Davenport-Heilbronn type functions are such `F`, with the
  same variable and the same `s ↦ 1 - s` symmetry) no realization exists. So
  the content of RH is the existence of a realization for `xi`, not the
  identification of the variable.

No realization for `GppFE.riemannXi` is constructed or assumed here. RH is
open. Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.
-/

namespace GppHilbertPolyaTarget

open Complex Module.End

/-- A Hilbert-Polya realization of the zeros of `F`: a symmetric operator on a
complex inner product space whose eigenvalues include `-i (rho - 1/2)` for
every zero `rho` of `F`, i.e. `rho = 1/2 + i lambda`. -/
structure HilbertPolyaRealization (F : ℂ → ℂ) where
  /-- The carrier (for an unbounded operator, its domain). -/
  H : Type
  [instNormed : NormedAddCommGroup H]
  [instInner : InnerProductSpace ℂ H]
  /-- The operator. -/
  T : H →ₗ[ℂ] H
  /-- Symmetry: `⟪T x, y⟫ = ⟪x, T y⟫`. -/
  symm : T.IsSymmetric
  /-- Every zero is a spectral point `1/2 + i lambda`. -/
  zero_eigen : ∀ ρ : ℂ, F ρ = 0 → HasEigenvalue T (-I * (ρ - 1 / 2))

attribute [instance] HilbertPolyaRealization.instNormed
  HilbertPolyaRealization.instInner

/-- **A realization puts every zero on the line.** -/
theorem re_eq_half_of_realization {F : ℂ → ℂ} (R : HilbertPolyaRealization F)
    {ρ : ℂ} (hρ : F ρ = 0) : ρ.re = 1 / 2 := by
  have h := R.symm.conj_eigenvalue_eq_self (R.zero_eigen ρ hρ)
  have him := congrArg Complex.im h
  simp only [Complex.conj_im, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im] at him
  norm_num at him
  linarith

/-- **Contrapositive: a zero off the line rules out any realization.** Since
functions sharing the variable `s` and the symmetry `s ↦ 1 - s` can have such
zeros, the realization, not the variable, carries the content of RH. -/
theorem no_realization_of_off_line_zero {F : ℂ → ℂ} {ρ : ℂ} (hρ : F ρ = 0)
    (hoff : ρ.re ≠ 1 / 2) : IsEmpty (HilbertPolyaRealization F) :=
  ⟨fun R => hoff (re_eq_half_of_realization R hρ)⟩

/-- A realization for the entire completed xi puts its zeros on the line. (The
legacy product `GppFE.riemannXi` has spurious zeros at 0 and 1, so it admits no
realization; the entire `GppLogDerivZeroFree.xi` is the right target.) -/
theorem xi_zeros_on_line_of_realization (R : HilbertPolyaRealization GppLogDerivZeroFree.xi) :
    ∀ ρ : ℂ, GppLogDerivZeroFree.xi ρ = 0 → ρ.re = 1 / 2 :=
  fun _ hρ => re_eq_half_of_realization R hρ

/-- **Conditional RH.** A realization for the entire xi (not constructed) gives
Mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_realization (R : HilbertPolyaRealization GppLogDerivZeroFree.xi) :
    RiemannHypothesis :=
  GppConditionalWeightState.riemannHypothesis_of_entire_xi_zeros_on_line
    (xi_zeros_on_line_of_realization R)

end GppHilbertPolyaTarget

#print axioms GppHilbertPolyaTarget.re_eq_half_of_realization
#print axioms GppHilbertPolyaTarget.no_realization_of_off_line_zero
