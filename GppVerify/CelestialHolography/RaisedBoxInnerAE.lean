import GppVerify.CelestialHolography.RaisedBoxConcreteMoment
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Tactic

/-!
# Almost-everywhere inner-slice regulator limit for the raised box

The scalar-box proof is organized as nested interval dominated convergence.
At the innermost stage, for fixed strict-interior `x₁,x₂`, the only point of
`Ioc 0 (1-x₁-x₂)` where strict simplex interior can fail is the upper endpoint.
Lebesgue measure is nonatomic, so that single endpoint may be discarded almost
everywhere. This file packages exactly the AE pointwise-convergence hypothesis
needed by the first interval-DCT step.
-/

namespace GppRaisedBoxInnerAE

open Filter Set MeasureTheory
open GppRaisedBoxConcreteMoment

/-- For fixed `x₁,x₂` in the strict two-dimensional base of the simplex, the
raised-box integrand tends to one for almost every point of the inner interval.
The sole exceptional point in `Ioc 0 (1-x₁-x₂)` is its upper endpoint. -/
theorem integrand_tendsto_one_ae_inner
    {S T x1 x2 : ℝ}
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 < x2)
    (hx12 : x1 + x2 < 1) :
    ∀ᵐ x3 : ℝ ∂volume,
      x3 ∈ Set.Ioc (0 : ℝ) (1 - x1 - x2) →
        Tendsto (fun ε : ℝ => integrand ε S T x1 x2 x3)
          (nhds 0) (nhds 1) := by
  have hne : ∀ᵐ x3 : ℝ ∂volume, x3 ≠ 1 - x1 - x2 := by
    simpa using (Set.countable_singleton (1 - x1 - x2)).ae_not_mem volume
  filter_upwards [hne] with x3 hx3ne
  intro hx3mem
  have hx3pos : 0 < x3 := hx3mem.1
  have hx3lt : x3 < 1 - x1 - x2 := lt_of_le_of_ne hx3mem.2 hx3ne
  have hxsum : x1 + x2 + x3 < 1 := by
    linarith
  exact integrand_tendsto_one hS hT hx1 hx2 hx3pos hxsum

end GppRaisedBoxInnerAE

#print axioms GppRaisedBoxInnerAE.integrand_tendsto_one_ae_inner
