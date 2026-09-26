import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# BPY two-copy angular law and the exact one-fifth Cayley variance

For two independent shape-two Gamma variables A,B, beta-gamma algebra gives

  Z = (A-B)/(A+B)

with density (3/4)(1-z^2) on [-1,1].  This is the first-coordinate law of a uniform
point on S^4.  The exact second moment is 1/5.

The probabilistic beta-gamma step is recorded in Discovery2.  This Lean file formalizes
the elementary density identities and the conditional scaling consequence only.
No RH claim is made.
-/

namespace GppBPYAngular

open intervalIntegral

noncomputable def angularDensity (z : ℝ) : ℝ :=
  (3 / 4 : ℝ) * (1 - z ^ 2)

theorem integral_one_neg_one :
    (∫ z in (-1 : ℝ)..1, (1 : ℝ)) = 2 := by
  norm_num

theorem integral_sq_neg_one :
    (∫ z in (-1 : ℝ)..1, z ^ 2) = 2 / 3 := by
  rw [integral_pow]
  norm_num

theorem integral_fourth_neg_one :
    (∫ z in (-1 : ℝ)..1, z ^ 4) = 2 / 5 := by
  rw [integral_pow]
  norm_num

/-- The S^4 coordinate density is normalized. -/
theorem angularDensity_normalized :
    (∫ z in (-1 : ℝ)..1, angularDensity z) = 1 := by
  unfold angularDensity
  have h1 := integral_one_neg_one
  have h2 := integral_sq_neg_one
  rw [show (fun z : ℝ => (3 / 4 : ℝ) * (1 - z ^ 2)) =
      (fun z : ℝ => (3 / 4 : ℝ) * 1 - (3 / 4 : ℝ) * z ^ 2) by
        funext z; ring]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h1, h2]
    norm_num
  · exact (continuous_const.mul continuous_const).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _

/-- Exact second moment E[Z^2]=1/5. -/
theorem angularDensity_second_moment :
    (∫ z in (-1 : ℝ)..1, z ^ 2 * angularDensity z) = 1 / 5 := by
  unfold angularDensity
  have h2 := integral_sq_neg_one
  have h4 := integral_fourth_neg_one
  rw [show (fun z : ℝ => z ^ 2 * ((3 / 4 : ℝ) * (1 - z ^ 2))) =
      (fun z : ℝ => (3 / 4 : ℝ) * z ^ 2 - (3 / 4 : ℝ) * z ^ 4) by
        funext z; ring]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h2, h4]
    norm_num
  · exact (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_pow 4)).intervalIntegrable _ _

/-- Odd first moment vanishes by direct polynomial integration. -/
theorem angularDensity_first_moment :
    (∫ z in (-1 : ℝ)..1, z * angularDensity z) = 0 := by
  unfold angularDensity
  rw [show (fun z : ℝ => z * ((3 / 4 : ℝ) * (1 - z ^ 2))) =
      (fun z : ℝ => (3 / 4 : ℝ) * z - (3 / 4 : ℝ) * z ^ 3) by
        funext z; ring]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_pow, integral_pow]
    norm_num
  · exact (continuous_const.mul (continuous_pow 1)).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_pow 3)).intervalIntegrable _ _

/-- Conditional on a radial factor r, the Cayley coordinate rZ has second moment r^2/5. -/
theorem scaled_angular_second_moment (r : ℝ) :
    (∫ z in (-1 : ℝ)..1, (r * z) ^ 2 * angularDensity z) = r ^ 2 / 5 := by
  rw [show (fun z : ℝ => (r * z) ^ 2 * angularDensity z) =
      (fun z : ℝ => r ^ 2 * (z ^ 2 * angularDensity z)) by
        funext z; ring]
  rw [intervalIntegral.integral_const_mul, angularDensity_second_moment]
  ring

/-- If |r|<=1, the conditional second moment is at most 1/5. -/
theorem scaled_angular_second_moment_le_one_fifth
    {r : ℝ} (hr : |r| ≤ 1) :
    r ^ 2 / 5 ≤ 1 / 5 := by
  have hrsq : r ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg r, sq_le_sq.mpr (by simpa [abs_nonneg] using hr)]
  nlinarith

/-- The one-fifth moment is exactly the square of the radius 1/sqrt(5). -/
theorem one_fifth_eq_inv_sqrt_five_sq :
    (1 / 5 : ℝ) = (1 / Real.sqrt 5) ^ 2 := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 5 ≠ 0 := by positivity
  field_simp [hs0]
  nlinarith

end GppBPYAngular
