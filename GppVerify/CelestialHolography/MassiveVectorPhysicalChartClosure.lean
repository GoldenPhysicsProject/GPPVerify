import GppVerify.CelestialHolography.MassiveVectorGenericDefect
import Mathlib.Tactic

/-!
# Physical-chart closure of the generic massive-vector mixed-helicity cut

The abstract mixed-helicity positivity theorem uses
`u = beta^2 sin(theta)^2 ∈ [0,1]` and assumes the physical denominator is nonzero.
The rational chart already proves the range of `u` and gives an exact formula for the
denominator.  This file closes those hypotheses directly in `(r,t)` coordinates.

The only denominator-zero point of the chart is the degenerate point `(r,t)=(0,0)`.
Consequently the exact `D_s=4` mixed-helicity baseline is strictly positive at every
nondegenerate rational-chart point.
-/

namespace GppMassiveVectorPhysicalChartClosure

open GppMassiveCutPhysicalCoordinates
open GppMassiveVectorGenericDefect

/-- The rational physical denominator is nonzero whenever `r^2+t^2` is nonzero. -/
theorem physicalDenominator_ne_zero
    {r t : ℝ} (hrt : r ^ 2 + t ^ 2 ≠ 0) :
    1 - betaCoord r * cosThetaCoord t ≠ 0 := by
  rw [one_sub_beta_mul_cosTheta]
  have hr : 1 + r ^ 2 ≠ 0 := by nlinarith [sq_nonneg r]
  have ht : 1 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  exact div_ne_zero (mul_ne_zero (by norm_num) hrt) (mul_ne_zero hr ht)

/-- The rational physical denominator vanishes exactly at the degenerate chart point. -/
theorem physicalDenominator_eq_zero_iff (r t : ℝ) :
    1 - betaCoord r * cosThetaCoord t = 0 ↔ r = 0 ∧ t = 0 := by
  rw [one_sub_beta_mul_cosTheta]
  have hr : 1 + r ^ 2 ≠ 0 := by nlinarith [sq_nonneg r]
  have ht : 1 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  have hden : (1 + r ^ 2) * (1 + t ^ 2) ≠ 0 := mul_ne_zero hr ht
  constructor
  · intro h
    have hmul := congrArg (fun z : ℝ => z * ((1 + r ^ 2) * (1 + t ^ 2))) h
    have hs : r ^ 2 + t ^ 2 = 0 := by
      simpa [hden] using hmul
    constructor <;> nlinarith [sq_nonneg r, sq_nonneg t]
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- The exact chart variable automatically supplies the abstract physical interval
hypotheses required by the mixed-helicity positivity theorem. -/
theorem mixedHelicityDs4Physical_chart_nonneg (r t : ℝ) :
    0 ≤ mixedHelicityDs4Physical
      (betaCoord r) (cosThetaCoord t) (mixedHelicityUCoord r t) := by
  rcases mixedHelicityUCoord_mem_unitInterval r t with ⟨hu0, hu1⟩
  exact mixedHelicityDs4Physical_nonneg (betaCoord r) (cosThetaCoord t) hu0 hu1

/-- **Physical-chart strict closure.**  Away from `(r,t)=(0,0)`, the generic
mixed-helicity `D_s=4` cut baseline is strictly positive. -/
theorem mixedHelicityDs4Physical_chart_pos
    {r t : ℝ} (hdeg : ¬ (r = 0 ∧ t = 0)) :
    0 < mixedHelicityDs4Physical
      (betaCoord r) (cosThetaCoord t) (mixedHelicityUCoord r t) := by
  rcases mixedHelicityUCoord_mem_unitInterval r t with ⟨hu0, hu1⟩
  apply mixedHelicityDs4Physical_pos (betaCoord r) (cosThetaCoord t) hu0 hu1
  intro hden
  exact hdeg ((physicalDenominator_eq_zero_iff r t).mp hden)

end GppMassiveVectorPhysicalChartClosure

#print axioms GppMassiveVectorPhysicalChartClosure.physicalDenominator_eq_zero_iff
#print axioms GppMassiveVectorPhysicalChartClosure.mixedHelicityDs4Physical_chart_nonneg
#print axioms GppMassiveVectorPhysicalChartClosure.mixedHelicityDs4Physical_chart_pos
