import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

/-!
# Positive fermionic determinants have imaginary-axis zeros

A finite positive one-particle operator with eigenvalues `lambda_i > 0` has fermionic
partition determinant

  F(z) = prod_i (1 + lambda_i z^2).

Every zero of `F` is purely imaginary.  This is the finite algebraic core of the operator
target

  F(z) = det(I + z^2 A),  A >= 0,

for the centered Riemann function.  In the infinite trace-class setting, such a determinant
representation would force all zeros onto the imaginary axis and hence imply RH after the
usual centering `z = s - 1/2`.

This file proves only the finite root-localization theorem.  It does not construct the
arithmetic positive operator `A`.
-/

namespace GppFiniteFermionicDeterminantCriticalZeros

open Complex

/-- A single positive fermionic factor can vanish only at a purely imaginary point. -/
theorem single_positive_factor_zero_implies_re_zero
    (lambda : ℝ) (hlambda : 0 < lambda) (z : ℂ)
    (hzero : 1 + (lambda : ℂ) * z^2 = 0) :
    z.re = 0 := by
  have hre := congrArg Complex.re hzero
  have him := congrArg Complex.im hzero
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have him' : z.re * z.im + z.im * z.re = 0 :=
    him.resolve_left (ne_of_gt hlambda)
  by_contra hz
  have himz : z.im = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im = 0 by nlinarith [him']) with h | h
    · exact (hz h).elim
    · exact h
  rw [himz] at hre
  simp at hre
  nlinarith [sq_nonneg z.re]

/-- A finite product of positive fermionic factors has only imaginary-axis zeros. -/
theorem finite_positive_det_zero_implies_re_zero
    {ι : Type*} [Fintype ι]
    (lambda : ι → ℝ) (hlambda : ∀ i, 0 < lambda i)
    (z : ℂ)
    (hzero : ∏ i, (1 + (lambda i : ℂ) * z^2) = 0) :
    z.re = 0 := by
  classical
  rw [Finset.prod_eq_zero_iff] at hzero
  rcases hzero with ⟨i, hi, hfac⟩
  exact single_positive_factor_zero_implies_re_zero (lambda i) (hlambda i) z hfac

/-- After centering `z = s - 1/2`, the same statement is the Riemann critical line. -/
theorem finite_positive_det_zero_forces_critical_line
    {ι : Type*} [Fintype ι]
    (lambda : ι → ℝ) (hlambda : ∀ i, 0 < lambda i)
    (s : ℂ)
    (hzero : ∏ i, (1 + (lambda i : ℂ) * (s - (1 / 2 : ℂ))^2) = 0) :
    s.re = (1 / 2 : ℝ) := by
  have hz := finite_positive_det_zero_implies_re_zero lambda hlambda
    (s - (1 / 2 : ℂ)) hzero
  simp [Complex.sub_re] at hz
  linarith

end GppFiniteFermionicDeterminantCriticalZeros
