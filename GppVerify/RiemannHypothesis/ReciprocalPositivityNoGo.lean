import Mathlib.Tactic

/-!
# Reciprocal symmetry plus coefficient positivity does not localize zeros

A recurring temptation in RH arguments is to combine an inversion/functional-equation
symmetry with a manifestly positive set of coefficients and conclude that all zeros must
lie on the symmetry locus.  The elementary reciprocal polynomial

    P(w) = 2 w^2 + 5 w + 2 = (2w+1)(w+2)

is a sharp counterexample.

It has strictly positive coefficients and exact reciprocal symmetry

    w^2 P(1/w) = P(w),

but its two roots are `-2` and `-1/2`, a reciprocal pair lying off the unit circle.
Therefore inversion symmetry and elementary positivity, even together, are insufficient for
zero localization.  The arithmetic RH programme needs the stronger Weil / reflection / Gram
positivity condition, not merely functional-equation symmetry plus positive coefficients.
-/

namespace GppReciprocalPositivityNoGo

/-- Positive reciprocal quadratic used as the counterexample. -/
def reciprocalPositivePoly (w : ℝ) : ℝ := 2 * w^2 + 5 * w + 2

/-- All three coefficients are strictly positive. -/
theorem coefficients_positive :
    (0 : ℝ) < 2 ∧ (0 : ℝ) < 5 ∧ (0 : ℝ) < 2 := by
  norm_num

/-- Exact factorization. -/
theorem reciprocalPositivePoly_factor (w : ℝ) :
    reciprocalPositivePoly w = (2*w + 1) * (w + 2) := by
  simp [reciprocalPositivePoly]
  ring

/-- Exact reciprocal symmetry away from the origin. -/
theorem reciprocal_symmetry {w : ℝ} (hw : w ≠ 0) :
    w^2 * reciprocalPositivePoly (1 / w) = reciprocalPositivePoly w := by
  simp [reciprocalPositivePoly]
  field_simp [hw]
  ring

/-- The outer reciprocal root. -/
theorem root_neg_two : reciprocalPositivePoly (-2) = 0 := by
  norm_num [reciprocalPositivePoly]

/-- The inner reciprocal root. -/
theorem root_neg_half : reciprocalPositivePoly (-(1/2 : ℝ)) = 0 := by
  norm_num [reciprocalPositivePoly]

/-- `-2` is not on the unit circle. -/
theorem root_neg_two_off_unit : |(-2 : ℝ)| ≠ 1 := by
  norm_num

/-- `-1/2` is not on the unit circle. -/
theorem root_neg_half_off_unit : |(-(1/2 : ℝ))| ≠ 1 := by
  norm_num

/-- The two roots are reciprocal to one another. -/
theorem roots_reciprocal : (-2 : ℝ)⁻¹ = -(1/2 : ℝ) := by
  norm_num

/-- Capstone no-go: there exists a zero of a positive-coefficient reciprocal polynomial
strictly off the symmetry locus `|w|=1`. -/
theorem positive_reciprocal_does_not_force_unit_circle :
    ∃ w : ℝ,
      reciprocalPositivePoly w = 0 ∧ |w| ≠ 1 := by
  refine ⟨-2, root_neg_two, ?_⟩
  exact root_neg_two_off_unit

end GppReciprocalPositivityNoGo
