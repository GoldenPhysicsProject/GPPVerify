import Mathlib.Tactic

/-!
# Algebra of the mu^4 dimension-shift rational limit

Discovery2 identifies the scalar-integral relation
`I4^(4-2ε)[mu^4] = -ε(1-ε) I4^(8-2ε)` and the universal raised-box
pole residue `ε * I4^(8-2ε) -> 1/6` in the stated normalization.

This file formalizes the exact algebraic cancellation underlying the finite `-1/6`
limit. The analytic Feynman-integral residue itself is not encoded here.
-/

namespace GppMu4DimensionShift

open Filter

/-- Exact Gamma-recursion polynomial appearing in the `mu^4` dimension shift. -/
def shiftFactor (ε : ℝ) : ℝ := -ε * (1 - ε)

/-- Multiplying the shift factor by the universal box pole `1/(6ε)` cancels
`ε` exactly away from `ε=0`. -/
theorem shiftFactor_mul_boxPole {ε : ℝ} (hε : ε ≠ 0) :
    shiftFactor ε * (1 / (6 * ε)) = -(1 - ε) / 6 := by
  unfold shiftFactor
  field_simp [hε]
  ring

/-- The dimension-shift product depends only on the *scaled* raised-box integral
`ε * I`.  Consequently the analytic input needed for the finite rational term is
the residue limit `ε * I(ε) -> 1/6`; a full Laurent estimate
`I(ε) = 1/(6ε) + O(1)` is stronger than necessary for this cancellation. -/
theorem shiftFactor_mul_eq_scaledResidue (ε I : ℝ) :
    shiftFactor ε * I = -(1 - ε) * (ε * I) := by
  unfold shiftFactor
  ring

/-- Pointwise version of the residue reduction: once `ε * I = r` is known, the
whole dimension-shift product is exactly `-(1-ε) r`. -/
theorem shiftFactor_mul_of_scaledIntegral {ε I r : ℝ} (h : ε * I = r) :
    shiftFactor ε * I = -(1 - ε) * r := by
  rw [shiftFactor_mul_eq_scaledResidue, h]

/-- **Limit-transfer form of the dimension shift.** On any filter along which
`ε -> 0`, if the scaled raised-dimensional integral satisfies `ε I(ε) -> 1/6`,
then the `mu^4` dimension-shift product tends to the finite rational value `-1/6`.
Thus the analytic amplitude input is exactly the residue limit, not a full Laurent
expansion. -/
theorem tendsto_shiftFactor_mul_of_scaledResidue
    {I : ℝ → ℝ} {l : Filter ℝ}
    (hε : Tendsto (fun ε : ℝ => ε) l (nhds 0))
    (hres : Tendsto (fun ε : ℝ => ε * I ε) l (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => shiftFactor ε * I ε) l (nhds (-(1 / 6 : ℝ))) := by
  have hfac : Tendsto (fun ε : ℝ => -(1 - ε)) l (nhds (-1)) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) l (nhds 1) := tendsto_const_nhds
    simpa using (hone.sub hε).neg
  have hmul := hfac.mul hres
  convert hmul using 1
  · funext ε
    exact shiftFactor_mul_eq_scaledResidue ε (I ε)
  · ring

/-- The finite residue tends algebraically to `-1/6`; at the exact endpoint this
is simply the value of the regularized closed expression. -/
theorem regularizedResidue_at_zero :
    (-(1 - (0 : ℝ)) / 6) = -(1 / 6 : ℝ) := by
  norm_num

/-- Difference from the rational limit is exactly linear in the regulator. -/
theorem regularizedResidue_error (ε : ℝ) :
    (-(1 - ε) / 6) - (-(1 / 6 : ℝ)) = ε / 6 := by
  ring

end GppMu4DimensionShift

#print axioms GppMu4DimensionShift.shiftFactor_mul_boxPole
#print axioms GppMu4DimensionShift.shiftFactor_mul_eq_scaledResidue
#print axioms GppMu4DimensionShift.shiftFactor_mul_of_scaledIntegral
#print axioms GppMu4DimensionShift.tendsto_shiftFactor_mul_of_scaledResidue
#print axioms GppMu4DimensionShift.regularizedResidue_error
