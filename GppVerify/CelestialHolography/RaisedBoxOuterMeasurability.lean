import GppVerify.CelestialHolography.RaisedBoxMiddleDCT
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Raised-box outer-slice measurability

The final dominated-convergence step treats the already-integrated `(x2,x3)`
slice as a function of `x1`.  Variable affine endpoints are handled by a
single jointly measurable indicator on `((x1,x2),x3)`:

  0 < x2 ≤ 1 - x1,    0 < x3 ≤ 1 - x1 - x2.

Integrating this whole-line model first in `x3` and then in `x2` gives a
strongly measurable function of `x1`. On the physical outer interval it is
exactly the nested interval integral used by `simplexMoment`.
-/

namespace GppRaisedBoxOuterMeasurability

open MeasureTheory Real
open GppRaisedBoxConcreteMoment
open GppRaisedBoxMiddleMeasurability

/-- The two inner affine-simplex inequalities, with `x1` left as a parameter
coordinate. The outer condition `0 ≤ x1 ≤ 1` is supplied by the final interval
integral rather than built into this region. -/
def outerInnerRegion : Set ((ℝ × ℝ) × ℝ) :=
  {p | (0 < p.1.2 ∧ p.1.2 ≤ 1 - p.1.1) ∧
       (0 < p.2 ∧ p.2 ≤ 1 - p.1.1 - p.1.2)}

/-- The three-variable affine inner region is Borel measurable. -/
theorem measurableSet_outerInnerRegion : MeasurableSet outerInnerRegion := by
  unfold outerInnerRegion
  exact
    ((measurableSet_lt measurable_const measurable_fst.snd).inter
      (measurableSet_le measurable_fst.snd
        (measurable_const.sub measurable_fst.fst))).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd
          ((measurable_const.sub measurable_fst.fst).sub measurable_fst.snd)))

/-- The concrete raised-box integrand is jointly strongly measurable in all
three simplex coordinates. -/
theorem full_integrand_stronglyMeasurable
    (ε S T : ℝ) :
    StronglyMeasurable
      (fun p : (ℝ × ℝ) × ℝ => integrand ε S T p.1.1 p.1.2 p.2) := by
  have hQ : Continuous
      (fun p : (ℝ × ℝ) × ℝ => Q S T p.1.1 p.1.2 p.2) := by
    unfold Q x4
    fun_prop
  have hm : Measurable
      (fun p : (ℝ × ℝ) × ℝ => integrand ε S T p.1.1 p.1.2 p.2) := by
    unfold integrand
    exact hQ.measurable.pow_const (-ε)
  exact hm.stronglyMeasurable

/-- Joint strong measurability survives restriction to the affine two-inner
simplex region. -/
theorem outer_indicator_stronglyMeasurable
    (ε S T : ℝ) :
    StronglyMeasurable
      (outerInnerRegion.indicator
        (fun p : (ℝ × ℝ) × ℝ => integrand ε S T p.1.1 p.1.2 p.2)) := by
  exact (full_integrand_stronglyMeasurable ε S T).indicator
    measurableSet_outerInnerRegion

/-- After integrating out `x3`, the whole-line inner representative is jointly
strongly measurable in `(x1,x2)`. -/
theorem wholeLine_x3_integral_stronglyMeasurable
    (ε S T : ℝ) :
    StronglyMeasurable
      (fun q : ℝ × ℝ =>
        ∫ x3 : ℝ,
          outerInnerRegion.indicator
            (fun p : (ℝ × ℝ) × ℝ => integrand ε S T p.1.1 p.1.2 p.2)
            (q, x3)) := by
  exact (outer_indicator_stronglyMeasurable ε S T).integral_prod_right'

/-- Integrating the measurable whole-line representative once more in `x2`
produces a strongly measurable function of the outer variable `x1`. -/
theorem wholeLine_middle_integral_stronglyMeasurable
    (ε S T : ℝ) :
    StronglyMeasurable
      (fun x1 : ℝ =>
        ∫ x2 : ℝ,
          ∫ x3 : ℝ,
            outerInnerRegion.indicator
              (fun p : (ℝ × ℝ) × ℝ => integrand ε S T p.1.1 p.1.2 p.2)
              ((x1, x2), x3)) := by
  exact (wholeLine_x3_integral_stronglyMeasurable ε S T).integral_prod_right'

/-- On a physical outer slice, the whole-line double-indicator model is exactly
the nested variable-endpoint interval integral used by the raised-box moment. -/
theorem wholeLine_middle_integral_eq_intervalIntegral
    {ε S T x1 : ℝ} (hx10 : 0 ≤ x1) (hx11 : x1 ≤ 1) :
    (∫ x2 : ℝ,
      ∫ x3 : ℝ,
        outerInnerRegion.indicator
          (fun p : (ℝ × ℝ) × ℝ => integrand ε S T p.1.1 p.1.2 p.2)
          ((x1, x2), x3)) =
      ∫ x2 : ℝ in (0 : ℝ)..(1 - x1),
        ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
          integrand ε S T x1 x2 x3 := by
  have hL : 0 ≤ 1 - x1 := by linarith
  have hfun :
      (fun x2 : ℝ =>
        ∫ x3 : ℝ,
          outerInnerRegion.indicator
            (fun p : (ℝ × ℝ) × ℝ => integrand ε S T p.1.1 p.1.2 p.2)
            ((x1, x2), x3)) =
      (Set.Ioc (0 : ℝ) (1 - x1)).indicator
        (fun x2 : ℝ =>
          ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
            integrand ε S T x1 x2 x3) := by
    funext x2
    by_cases hx2 : x2 ∈ Set.Ioc (0 : ℝ) (1 - x1)
    · have hx2' : 0 < x2 ∧ x2 ≤ 1 - x1 := by
        simpa [Set.mem_Ioc] using hx2
      have hinner :
          (fun x3 : ℝ =>
            outerInnerRegion.indicator
              (fun p : (ℝ × ℝ) × ℝ => integrand ε S T p.1.1 p.1.2 p.2)
              ((x1, x2), x3)) =
          (innerRegion x1).indicator
            (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2) (x2, ·) := by
        funext x3
        simp [outerInnerRegion, innerRegion, hx2'.1, hx2'.2]
      rw [hinner, wholeLine_inner_integral_eq_intervalIntegral (by linarith [hx2'.2])]
      simp [hx2]
    · have hzero :
          (fun x3 : ℝ =>
            outerInnerRegion.indicator
              (fun p : (ℝ × ℝ) × ℝ => integrand ε S T p.1.1 p.1.2 p.2)
              ((x1, x2), x3)) = fun _x3 : ℝ => 0 := by
        funext x3
        have hx2' : ¬ (0 < x2 ∧ x2 ≤ 1 - x1) := by
          simpa [Set.mem_Ioc] using hx2
        simp [outerInnerRegion, hx2']
      rw [hzero]
      simp [hx2]
  rw [hfun, integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le hL]

end GppRaisedBoxOuterMeasurability

#print axioms GppRaisedBoxOuterMeasurability.measurableSet_outerInnerRegion
#print axioms GppRaisedBoxOuterMeasurability.full_integrand_stronglyMeasurable
#print axioms GppRaisedBoxOuterMeasurability.outer_indicator_stronglyMeasurable
#print axioms GppRaisedBoxOuterMeasurability.wholeLine_x3_integral_stronglyMeasurable
#print axioms GppRaisedBoxOuterMeasurability.wholeLine_middle_integral_stronglyMeasurable
#print axioms GppRaisedBoxOuterMeasurability.wholeLine_middle_integral_eq_intervalIntegral
