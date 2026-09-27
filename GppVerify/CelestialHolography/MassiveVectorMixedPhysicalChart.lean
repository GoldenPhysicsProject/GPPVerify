import GppVerify.CelestialHolography.MassiveVectorGenericDefect

/-!
# Mixed-helicity positivity on the rational physical chart

This file removes the free interval hypotheses from the mixed-helicity `D_s=4`
positivity statement by specializing `u` to the exact rational massive-cut chart

  u(r,t) = beta(r)^2 sin(theta(t))^2.

The range `0 ≤ u ≤ 1` is proved in `MassiveCutPhysicalCoordinates`.
-/

namespace GppMassiveVectorMixedPhysicalChart

open GppMassiveCutPhysicalCoordinates
open GppMassiveVectorGenericDefect

/-- The mixed-helicity `D_s=4` cut baseline is nonnegative on every point of the
rational physical chart, with no separately assumed range condition. -/
theorem mixedHelicityDs4Physical_chart_nonneg (r t : ℝ) :
    0 ≤ mixedHelicityDs4Physical
      (betaCoord r) (cosThetaCoord t) (mixedHelicityUCoord r t) := by
  rcases mixedHelicityUCoord_mem_unitInterval r t with ⟨hu0, hu1⟩
  exact mixedHelicityDs4Physical_nonneg _ _ hu0 hu1

/-- Away from the exact cut denominator zero, the chart-specialized mixed-helicity
baseline is strictly positive. -/
theorem mixedHelicityDs4Physical_chart_pos
    {r t : ℝ} (hden : 1 - betaCoord r * cosThetaCoord t ≠ 0) :
    0 < mixedHelicityDs4Physical
      (betaCoord r) (cosThetaCoord t) (mixedHelicityUCoord r t) := by
  rcases mixedHelicityUCoord_mem_unitInterval r t with ⟨hu0, hu1⟩
  exact mixedHelicityDs4Physical_pos _ _ hu0 hu1 hden

end GppMassiveVectorMixedPhysicalChart

#print axioms GppMassiveVectorMixedPhysicalChart.mixedHelicityDs4Physical_chart_nonneg
#print axioms GppMassiveVectorMixedPhysicalChart.mixedHelicityDs4Physical_chart_pos
