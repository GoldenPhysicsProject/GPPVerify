import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Elementary regulator bounds for the explicit scalar-box remainder

The Discovery2 explicit remainder theorem uses two uniform small-argument bounds.
This file begins the analytic promotion with the logarithmic estimate

  |log(1-x)| <= x/(1-x),  0<=x<1.

The dilogarithm estimate is kept separate until its exact Mathlib/polylog series
interface is pinned.
-/

namespace GppRegulatorElementaryBounds

/-- **Small-argument logarithm bound** used throughout the regulated scalar-box remainder. -/
theorem abs_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |Real.log (1 - x)| ≤ x / (1 - x) := by
  have hpos : 0 < 1 - x := sub_pos.mpr hx1
  have hle1 : 1 - x ≤ 1 := by linarith
  have hlog : Real.log (1 - x) ≤ 0 := Real.log_nonpos hpos.le hle1
  rw [abs_of_nonpos hlog]
  have hinvpos : 0 < (1 - x)⁻¹ := inv_pos.mpr hpos
  have h := Real.log_le_sub_one_of_pos hinvpos
  rw [Real.log_inv] at h
  have hid : (1 - x)⁻¹ - 1 = x / (1 - x) := by
    field_simp [hpos.ne']
    ring
  rw [hid] at h
  exact h

end GppRegulatorElementaryBounds

#print axioms GppRegulatorElementaryBounds.abs_log_one_sub_le
