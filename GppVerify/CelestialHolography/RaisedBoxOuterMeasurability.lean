import GppVerify.CelestialHolography.RaisedBoxConcreteMoment
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Raised-box outer-coordinate measurability

The final regulator-removal step needs measurability in the outer affine
coordinate `x1` after both inner coordinates have been integrated out.  Rather
than treating the two variable interval endpoints as primitive parameterized
integrals, this file embeds the whole affine three-simplex as one measurable
subset of `ℝ × (ℝ × ℝ)` and uses product integration.

This is the outer analogue of the measurable-strip construction already used
for the middle-coordinate DCT.  A subsequent bridge identifies this measurable
product-fiber representation with the original nested interval integral on the
physical outer interval.
-/

namespace GppRaisedBoxOuterMeasurability

open MeasureTheory
open GppRaisedBoxConcreteMoment

/-- The standard affine three-simplex, grouped as `x1 × (x2 × x3)` so that
`integral_prod_right'` integrates the two inner coordinates as one product
fiber.  It is written directly as an intersection of four half-spaces so that
the measurability proof has exactly the same set expression. -/
def fullSimplexSet : Set (ℝ × (ℝ × ℝ)) :=
  {p | 0 ≤ p.1} ∩
    {p | 0 ≤ p.2.1} ∩
      {p | 0 ≤ p.2.2} ∩
        {p | p.1 + p.2.1 + p.2.2 ≤ 1}

/-- The grouped affine three-simplex is Borel measurable. -/
theorem measurableSet_fullSimplexSet : MeasurableSet fullSimplexSet := by
  unfold fullSimplexSet
  have hx1 : Measurable (fun p : ℝ × (ℝ × ℝ) => p.1) := measurable_fst
  have hx2 : Measurable (fun p : ℝ × (ℝ × ℝ) => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hx3 : Measurable (fun p : ℝ × (ℝ × ℝ) => p.2.2) :=
    measurable_snd.comp measurable_snd
  have hzero : Measurable (fun _ : ℝ × (ℝ × ℝ) => (0 : ℝ)) := measurable_const
  have hone : Measurable (fun _ : ℝ × (ℝ × ℝ) => (1 : ℝ)) := measurable_const
  exact
    (((measurableSet_le hzero hx1).inter
      (measurableSet_le hzero hx2)).inter
      (measurableSet_le hzero hx3)).inter
      (measurableSet_le ((hx1.add hx2).add hx3) hone)

/-- The raised-box integrand is jointly Borel measurable in all three affine
simplex coordinates. -/
theorem integrand_measurable_all (ε S T : ℝ) :
    Measurable
      (fun p : ℝ × (ℝ × ℝ) =>
        integrand ε S T p.1 p.2.1 p.2.2) := by
  unfold integrand
  apply Measurable.pow_const
  unfold Q x4
  fun_prop

/-- Extending the full three-coordinate integrand by zero off the affine
simplex preserves measurability. -/
theorem fullSimplexIntegrand_measurable (ε S T : ℝ) :
    Measurable
      (fullSimplexSet.indicator
        (fun p : ℝ × (ℝ × ℝ) =>
          integrand ε S T p.1 p.2.1 p.2.2)) := by
  exact (integrand_measurable_all ε S T).indicator measurableSet_fullSimplexSet

/-- Product integration over the two inner coordinates gives a strongly
measurable function of the remaining outer coordinate.  This is the
measure-theoretic half of the final outer-DCT interface. -/
theorem fullSimplexFiberIntegral_stronglyMeasurable (ε S T : ℝ) :
    StronglyMeasurable
      (fun x1 : ℝ =>
        ∫ p : ℝ × ℝ,
          (fullSimplexSet.indicator
            (fun q : ℝ × (ℝ × ℝ) =>
              integrand ε S T q.1 q.2.1 q.2.2)) (x1, p)) := by
  exact
    (fullSimplexIntegrand_measurable ε S T).stronglyMeasurable.integral_prod_right'

end GppRaisedBoxOuterMeasurability

#print axioms GppRaisedBoxOuterMeasurability.measurableSet_fullSimplexSet
#print axioms GppRaisedBoxOuterMeasurability.integrand_measurable_all
#print axioms GppRaisedBoxOuterMeasurability.fullSimplexIntegrand_measurable
#print axioms GppRaisedBoxOuterMeasurability.fullSimplexFiberIntegral_stronglyMeasurable