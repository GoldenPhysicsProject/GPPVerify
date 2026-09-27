import GppVerify.CelestialHolography.RaisedBoxOuterFubiniClosure
import GppVerify.CelestialHolography.RaisedBoxStripIntegralBridge
import Mathlib.Tactic

/-!
# Raised-box outer nested bridge

This file composes the certified physical Fubini closure with the strip-to-
interval bridge.  The fixed-`x1` two-dimensional Lebesgue fiber is therefore
identified directly with the variable-endpoint inner interval integral used by
the original nested raised-box moment, under only the physical regulator and
Euclidean-kinematic assumptions.
-/

namespace GppRaisedBoxOuterNestedBridge

open MeasureTheory
open GppRaisedBoxConcreteMoment
open GppRaisedBoxOuterMeasurability
open GppRaisedBoxOuterFubiniClosure
open GppRaisedBoxStripIntegralBridge

/-- Under the physical raised-box hypotheses, the fixed-`x1` full-simplex
fiber is exactly the whole-line `x2` integral of the original affine inner
interval integral.  This eliminates the measurable strip representation after
it has served its Fubini purpose. -/
theorem fullSimplexFiberIntegral_eq_nestedInner_of_physical_bounds
    {δ ε S T x1 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx1lt : x1 < 1) :
    (∫ p : ℝ × ℝ,
      (fullSimplexSet.indicator
        (fun q : ℝ × (ℝ × ℝ) =>
          integrand ε S T q.1 q.2.1 q.2.2)) (x1, p)) =
      ∫ x2 : ℝ,
        (Set.Icc (0 : ℝ) (1 - x1)).indicator
          (fun y : ℝ =>
            ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - y),
              integrand ε S T x1 y x3) x2 := by
  rw [fullSimplexFiberIntegral_eq_iteratedStrip_of_physical_bounds
    hδ0 hδ1 hε0 hεδ hS hT hx1 hx1lt]
  apply integral_congr_ae
  filter_upwards [] with x2
  by_cases hx2 : x2 ∈ Set.Icc (0 : ℝ) (1 - x1)
  · rw [Set.indicator_of_mem hx2, Set.indicator_of_mem hx2]
    exact stripInnerIntegral_eq_intervalIntegral ε S T x1 x2 hx2
  · simp only [Set.indicator_of_not_mem hx2]

/-- The same physical fiber is exactly the original nested `x2`/`x3` interval
integral.  Both indicator layers introduced for product-measure arguments are
now gone; the result is in the coordinate form of `simplexMoment`. -/
theorem fullSimplexFiberIntegral_eq_nestedIntervals_of_physical_bounds
    {δ ε S T x1 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx1lt : x1 < 1) :
    (∫ p : ℝ × ℝ,
      (fullSimplexSet.indicator
        (fun q : ℝ × (ℝ × ℝ) =>
          integrand ε S T q.1 q.2.1 q.2.2)) (x1, p)) =
      ∫ x2 : ℝ in (0 : ℝ)..(1 - x1),
        ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
          integrand ε S T x1 x2 x3 := by
  rw [fullSimplexFiberIntegral_eq_nestedInner_of_physical_bounds
    hδ0 hδ1 hε0 hεδ hS hT hx1 hx1lt]
  have hle : (0 : ℝ) ≤ 1 - x1 := by linarith
  rw [MeasureTheory.integral_indicator measurableSet_Icc]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hle]

end GppRaisedBoxOuterNestedBridge

#print axioms GppRaisedBoxOuterNestedBridge.fullSimplexFiberIntegral_eq_nestedInner_of_physical_bounds
#print axioms GppRaisedBoxOuterNestedBridge.fullSimplexFiberIntegral_eq_nestedIntervals_of_physical_bounds
