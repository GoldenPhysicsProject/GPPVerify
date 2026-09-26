import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Golden reciprocal scale pair

This file isolates the exact algebra behind a possible golden-ratio role in the
reciprocal scale / inversion structure used elsewhere in the arithmetic conformal
program.  It deliberately proves only the algebraic facts: inversion alone does
not select the golden ratio.  The extra unit-splitting condition

  r - r⁻¹ = 1

is equivalent, for nonzero `r`, to the golden quadratic `r² = r + 1`.
Its squared reciprocal pair then has trace `3`, the first integer strictly above
the parabolic threshold `2` for a determinant-one reciprocal spectrum.
-/

namespace GppGoldenReciprocalScale

/-- The positive golden ratio, written locally to keep this module independent of
any physical normalization. -/
noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- The defining golden quadratic. -/
theorem goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  unfold goldenRatio
  nlinarith

/-- The golden ratio is strictly positive. -/
theorem goldenRatio_pos : 0 < goldenRatio := by
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  unfold goldenRatio
  nlinarith

/-- Hence the golden ratio is nonzero. -/
theorem goldenRatio_ne_zero : goldenRatio ≠ 0 := ne_of_gt goldenRatio_pos

/-- For any nonzero real scale, a unit separation between reciprocal partners is
exactly the golden quadratic relation. -/
theorem unit_split_iff_golden_quadratic {r : ℝ} (hr : r ≠ 0) :
    r - r⁻¹ = 1 ↔ r ^ 2 = r + 1 := by
  constructor
  · intro h
    have hmul := congrArg (fun x : ℝ => x * r) h
    field_simp [hr] at hmul
    nlinarith
  · intro h
    field_simp [hr]
    nlinarith

/-- Squaring a reciprocal unit-split pair produces a determinant-one reciprocal
pair whose sum is exactly `3`.  Algebraically this is the trace-three hyperbolic
spectrum associated with the golden split. -/
theorem sq_add_inv_sq_eq_three_of_unit_split
    {r : ℝ} (hr : r ≠ 0) (hsplit : r - r⁻¹ = 1) :
    r ^ 2 + (r⁻¹) ^ 2 = 3 := by
  have hprod : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have hsq := congrArg (fun x : ℝ => x ^ 2) hsplit
  nlinarith [sq_nonneg (r - r⁻¹)]

/-- The reciprocal partner of the golden ratio is `goldenRatio - 1`. -/
theorem goldenRatio_inv_eq_sub_one : goldenRatio⁻¹ = goldenRatio - 1 := by
  field_simp [goldenRatio_ne_zero]
  nlinarith [goldenRatio_sq]

/-- The golden reciprocal pair has exactly unit additive separation. -/
theorem goldenRatio_sub_inv : goldenRatio - goldenRatio⁻¹ = 1 := by
  rw [goldenRatio_inv_eq_sub_one]
  ring

/-- The unit scale is the exact multiplicative center of the reciprocal pair. -/
theorem goldenRatio_mul_inv : goldenRatio * goldenRatio⁻¹ = 1 := by
  exact mul_inv_cancel₀ goldenRatio_ne_zero

/-- The squared golden reciprocal pair has trace three. -/
theorem goldenRatio_sq_add_inv_sq :
    goldenRatio ^ 2 + (goldenRatio⁻¹) ^ 2 = 3 := by
  exact sq_add_inv_sq_eq_three_of_unit_split
    goldenRatio_ne_zero goldenRatio_sub_inv

/-- In logarithmic scale coordinates the reciprocal partners are symmetric about
zero, the logarithm of the unit scale. -/
theorem log_goldenRatio_inv : Real.log goldenRatio⁻¹ = -Real.log goldenRatio := by
  rw [Real.log_inv]

end GppGoldenReciprocalScale

#print axioms GppGoldenReciprocalScale.goldenRatio_sq
#print axioms GppGoldenReciprocalScale.unit_split_iff_golden_quadratic
#print axioms GppGoldenReciprocalScale.sq_add_inv_sq_eq_three_of_unit_split
#print axioms GppGoldenReciprocalScale.goldenRatio_sub_inv
#print axioms GppGoldenReciprocalScale.goldenRatio_sq_add_inv_sq
#print axioms GppGoldenReciprocalScale.log_goldenRatio_inv
