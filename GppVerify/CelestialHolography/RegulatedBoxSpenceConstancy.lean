import GppVerify.CelestialHolography.RegulatedBoxSpenceDerivativeKernel
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Constancy of the real Spence combination

The local derivative theorem already proves that the project's real Spence combination
has derivative zero at every point of `(0,1)`. Convexity of the interval therefore
upgrades pointwise stationarity to exact global constancy on the whole open interval.
-/

namespace GppRegulatedBoxSpenceConstancy

open Set
open GppRegulatedBoxSpenceDerivativeKernel

/-- The Spence combination is constant on the real unit interval. -/
theorem spenceCombination_eq_on_Ioo
    {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    spenceCombination x = spenceCombination y := by
  apply (convex_Ioo (0 : ℝ) 1).is_const_of_fderivWithin_eq_zero (𝕜 := ℝ)
  · intro z hz
    exact (spenceCombination_hasDerivAt_zero hz.1 hz.2).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [fderivWithin_of_isOpen isOpen_Ioo hz]
    rw [(spenceCombination_hasDerivAt_zero hz.1 hz.2).hasFDerivAt.fderiv]
    ext v
    simp
  · exact hx
  · exact hy

end GppRegulatedBoxSpenceConstancy

#print axioms GppRegulatedBoxSpenceConstancy.spenceCombination_eq_on_Ioo
