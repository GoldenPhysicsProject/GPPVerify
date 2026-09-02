import GppVerify.CelestialHolography.RaisedBoxConcreteMoment
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Raised-box middle-slice measurability

The middle dominated-convergence step integrates the already-physical `x3`
slice over a variable affine endpoint `1 - x1 - x2`.  Rather than asking for a
special variable-endpoint interval-integral measurability theorem, represent the
slice as a whole-line integral of a jointly measurable indicator on

  0 < x3 ∧ x3 ≤ 1 - x1 - x2.

Mathlib's product-integral measurability theorem then supplies the parameter
measurability in `x2`.  This module establishes that reusable measurable model;
it does not yet invoke the middle DCT.
-/

namespace GppRaisedBoxMiddleMeasurability

open MeasureTheory Real
open GppRaisedBoxConcreteMoment

/-- The affine inner-simplex region in `(x2,x3)` at fixed `x1`. -/
def innerRegion (x1 : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.2 ∧ p.2 ≤ 1 - x1 - p.1}

/-- The affine inner region is Borel measurable. -/
theorem measurableSet_innerRegion (x1 : ℝ) : MeasurableSet (innerRegion x1) := by
  unfold innerRegion
  exact
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_const.sub measurable_fst))

/-- At fixed regulator and outer coordinate, the concrete raised-box integrand
is jointly strongly measurable in `(x2,x3)`. -/
theorem joint_integrand_stronglyMeasurable
    (ε S T x1 : ℝ) :
    StronglyMeasurable
      (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2) := by
  have hQ : Continuous (fun p : ℝ × ℝ => Q S T x1 p.1 p.2) := by
    unfold Q x4
    fun_prop
  have hm : Measurable (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2) := by
    unfold integrand
    exact hQ.measurable.pow_const (-ε)
  exact hm.stronglyMeasurable

/-- Joint strong measurability survives restriction to the affine inner region. -/
theorem inner_indicator_stronglyMeasurable
    (ε S T x1 : ℝ) :
    StronglyMeasurable
      ((innerRegion x1).indicator
        (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2)) := by
  exact (joint_integrand_stronglyMeasurable ε S T x1).indicator
    (measurableSet_innerRegion x1)

/-- Consequently the whole-line representative of the variable-endpoint inner
integral is strongly measurable as a function of the middle variable `x2`. -/
theorem wholeLine_inner_integral_stronglyMeasurable
    (ε S T x1 : ℝ) :
    StronglyMeasurable
      (fun x2 : ℝ =>
        ∫ x3 : ℝ,
          (innerRegion x1).indicator
            (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2) (x2, x3)) := by
  exact (inner_indicator_stronglyMeasurable ε S T x1).integral_prod_right'

/-- On a physical middle slice, the measurable whole-line indicator model is
exactly the variable-endpoint interval integral used by the raised-box moment. -/
theorem wholeLine_inner_integral_eq_intervalIntegral
    {ε S T x1 x2 : ℝ} (hL : 0 ≤ 1 - x1 - x2) :
    (∫ x3 : ℝ,
      (innerRegion x1).indicator
        (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2) (x2, x3)) =
      ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
        integrand ε S T x1 x2 x3 := by
  have hfun :
      (fun x3 : ℝ =>
        (innerRegion x1).indicator
          (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2) (x2, x3)) =
      (Set.Ioc (0 : ℝ) (1 - x1 - x2)).indicator
        (fun x3 : ℝ => integrand ε S T x1 x2 x3) := by
    funext x3
    simp [innerRegion, Set.mem_Ioc]
  rw [hfun, integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le hL]

end GppRaisedBoxMiddleMeasurability

#print axioms GppRaisedBoxMiddleMeasurability.measurableSet_innerRegion
#print axioms GppRaisedBoxMiddleMeasurability.joint_integrand_stronglyMeasurable
#print axioms GppRaisedBoxMiddleMeasurability.inner_indicator_stronglyMeasurable
#print axioms GppRaisedBoxMiddleMeasurability.wholeLine_inner_integral_stronglyMeasurable
#print axioms GppRaisedBoxMiddleMeasurability.wholeLine_inner_integral_eq_intervalIntegral
