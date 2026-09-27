import GppVerify.CelestialHolography.RaisedBoxOuterFiberBridge
import GppVerify.CelestialHolography.RaisedBoxOuterProductIntegrability
import Mathlib.Tactic

/-!
# Raised-box outer Fubini closure

This file discharges the last abstract integrability hypothesis in the outer
fiber/Fubini bridge.  The product-integrability theorem is now fed directly
into the exact full-simplex section factorization, so the two-dimensional
Lebesgue fiber is identified with the iterated measurable strip integral under
only the physical regulator and Euclidean-kinematic assumptions.
-/

namespace GppRaisedBoxOuterFubiniClosure

open MeasureTheory
open GppRaisedBoxConcreteMoment
open GppRaisedBoxOuterMeasurability
open GppRaisedBoxOuterFiberBridge
open GppRaisedBoxOuterProductIntegrability

/-- Under the physical raised-box hypotheses, the fixed-`x1` full-simplex
fiber is Fubini-integrable and therefore equals its iterated `x2`/`x3` strip
representation.  No standalone `Integrable` hypothesis remains. -/
theorem fullSimplexFiberIntegral_eq_iteratedStrip_of_physical_bounds
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
            ∫ x3 : ℝ,
              ((innerSimplexStrip x1).indicator
                (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2))
                (y, x3)) x2 := by
  apply fullSimplexFiberIntegral_eq_iteratedStrip ε S T x1
  · exact ⟨le_of_lt hx1, le_of_lt hx1lt⟩
  · exact fullSimplexFiber_integrable
      hδ0 hδ1 hε0 hεδ hS hT hx1 hx1lt

end GppRaisedBoxOuterFubiniClosure

#print axioms GppRaisedBoxOuterFubiniClosure.fullSimplexFiberIntegral_eq_iteratedStrip_of_physical_bounds
