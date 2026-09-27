import Mathlib.Tactic

/-!
# A2 chamber normalization algebra for M2

This file proves only the final scalar normalization. The analytic identities
`I_R2 = 2*pi^2/15` and `I_Q = I_R2/3` are not assumed or encoded here; they remain
separate integral/chamber theorems to formalize.
-/

namespace GppA2ChamberNormalization

open Real

/-- If the positive-domain integral is `2*pi^2/45`, then the standard
`(2*pi)^(-2)` normalization is exactly `1/90`. -/
theorem normalized_two_loop_value :
    (2 * Real.pi ^ 2 / 45) / (2 * Real.pi) ^ 2 = (1 / 90 : ℝ) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  ring

/-- The chamber value obtained algebraically from one third of the audited
full-plane value `2*pi^2/15`. -/
theorem one_third_full_plane_value :
    (1 / 3 : ℝ) * (2 * Real.pi ^ 2 / 15) = 2 * Real.pi ^ 2 / 45 := by
  ring

/-- Combined final algebraic closure from the full-plane scalar value. -/
theorem full_plane_to_normalized_two_loop :
    (((1 / 3 : ℝ) * (2 * Real.pi ^ 2 / 15)) / (2 * Real.pi) ^ 2) =
      (1 / 90 : ℝ) := by
  rw [one_third_full_plane_value]
  exact normalized_two_loop_value

end GppA2ChamberNormalization

#print axioms GppA2ChamberNormalization.normalized_two_loop_value
#print axioms GppA2ChamberNormalization.one_third_full_plane_value
#print axioms GppA2ChamberNormalization.full_plane_to_normalized_two_loop
