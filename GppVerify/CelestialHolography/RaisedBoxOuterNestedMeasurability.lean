import GppVerify.CelestialHolography.RaisedBoxOuterNestedBridge
import Mathlib.Tactic

/-!
# Raised-box outer nested measurability

The final outer dominated-convergence step is written in the original nested
Feynman-parameter coordinates.  Joint product measurability was already
certified for the full affine simplex; the physical Fubini/nested bridge now
transfers that certificate to the actual two-inner-coordinate interval integral
on the strict outer simplex interval.
-/

namespace GppRaisedBoxOuterNestedMeasurability

open Filter Set MeasureTheory
open scoped Interval Topology
open GppRaisedBoxConcreteMoment
open GppRaisedBoxOuterMeasurability
open GppRaisedBoxOuterNestedBridge

/-- On the strict physical outer interval, the complete nested `x2`/`x3`
raised-box fiber is a.e. strongly measurable in `x1`.  This is the exact
measurability input for the final outer dominated-convergence assembly; the two
outer endpoints can subsequently be discarded as null sets. -/
theorem nestedInnerIntegral_aestronglyMeasurable_Ioo
    {δ ε S T : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T) :
    AEStronglyMeasurable
      (fun x1 : ℝ =>
        ∫ x2 : ℝ in (0 : ℝ)..(1 - x1),
          ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
            integrand ε S T x1 x2 x3)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  have hf :
      AEStronglyMeasurable
        (fun x1 : ℝ =>
          ∫ p : ℝ × ℝ,
            (fullSimplexSet.indicator
              (fun q : ℝ × (ℝ × ℝ) =>
                integrand ε S T q.1 q.2.1 q.2.2)) (x1, p))
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    (fullSimplexFiberIntegral_stronglyMeasurable ε S T).aestronglyMeasurable.restrict
  apply hf.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x1 hx1
  exact fullSimplexFiberIntegral_eq_nestedIntervals_of_physical_bounds
    hδ0 hδ1 hε0 hεδ hS hT hx1.1 hx1.2

end GppRaisedBoxOuterNestedMeasurability

#print axioms GppRaisedBoxOuterNestedMeasurability.nestedInnerIntegral_aestronglyMeasurable_Ioo
