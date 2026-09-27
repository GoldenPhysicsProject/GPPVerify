import GppVerify.CelestialHolography.RegulatedBoxLandenDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Constancy of the branch-free real Landen combination

The Landen derivative kernel vanishes at every point of `(0,1)`. Convexity of the
interval therefore upgrades pointwise stationarity to exact global constancy.
-/

namespace GppRegulatedBoxLandenConstancy

open Set
open GppRegulatedBoxLandenDerivative

/-- The real Landen combination is constant throughout `(0,1)`. -/
theorem landenCombination_eq_on_Ioo
    {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    landenCombination x = landenCombination y := by
  apply (convex_Ioo (0 : ℝ) 1).is_const_of_fderivWithin_eq_zero (𝕜 := ℝ)
  · intro z hz
    exact (landenCombination_hasDerivAt_zero hz.1 hz.2).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [fderivWithin_of_isOpen isOpen_Ioo hz]
    rw [(landenCombination_hasDerivAt_zero hz.1 hz.2).hasFDerivAt.fderiv]
    ext v
    simp
  · exact hx
  · exact hy

end GppRegulatedBoxLandenConstancy

#print axioms GppRegulatedBoxLandenConstancy.landenCombination_eq_on_Ioo
