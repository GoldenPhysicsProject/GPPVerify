import GppVerify.CelestialHolography.RegulatedBoxDilogDerivativeUnitDisk
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Branch-free real Landen derivative cancellation

For `0 < x < 1`, every dilogarithm argument in

  Li2(x/(1+x)) + Li2(-x) + (1/2) log(1+x)^2

lies in the real power-series domain `(-1,1)`.  The three derivatives cancel
identically.  This is the differential core of the real Landen identity, with no
complex logarithm or branch choice.
-/

namespace GppRegulatedBoxLandenDerivative

open GppRegulatedBoxDilogSeries
open GppRegulatedBoxDilogDerivative
open GppRegulatedBoxDilogDerivativeUnitDisk

/-- The real Landen combination before endpoint normalization. -/
noncomputable def landenCombination (x : ℝ) : ℝ :=
  li2Series (x / (1 + x)) + li2Series (-x) + (Real.log (1 + x)) ^ 2 / 2

/-- The Landen combination has zero derivative throughout `(0,1)`. -/
theorem landenCombination_hasDerivAt_zero
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt landenCombination 0 x := by
  have hdenpos : 0 < 1 + x := by linarith
  have hden : (1 + x : ℝ) ≠ 0 := ne_of_gt hdenpos
  have hy0 : 0 < x / (1 + x) := div_pos hx0 hdenpos
  have hy1 : x / (1 + x) < 1 := by
    apply (div_lt_one hdenpos).2
    linarith

  have hinner_raw :=
    (hasDerivAt_id x).div
      ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)) hden
  have hinner :
      HasDerivAt (fun t : ℝ => t / (1 + t)) (1 / (1 + x) ^ 2) x := by
    convert hinner_raw using 1 <;> field_simp [hden] <;> ring

  have hpos_base := hasDerivAt_li2Series hy0 hy1
  have hpos_comp := hpos_base.comp x hinner

  have hone_minus : 1 - x / (1 + x) = 1 / (1 + x) := by
    field_simp [hden]
  have hrecipne : (1 / (1 + x) : ℝ) ≠ 0 := one_div_ne_zero hden
  have hlogrecip : Real.log (1 / (1 + x)) = -Real.log (1 + x) := by
    have hm := Real.log_mul hrecipne hden
    have hmul : (1 / (1 + x)) * (1 + x) = (1 : ℝ) := by
      field_simp [hden]
    rw [hmul, Real.log_one] at hm
    linarith
  have hpos :
      HasDerivAt (fun t : ℝ => li2Series (t / (1 + t)))
        (Real.log (1 + x) / (x * (1 + x))) x := by
    rw [hone_minus, hlogrecip] at hpos_comp
    convert hpos_comp using 1 <;> field_simp [hx0.ne', hden] <;> ring

  have hneg_inner : HasDerivAt (fun t : ℝ => -t) (-1) x := by
    simpa using (hasDerivAt_id x).neg
  have hneg_base := hasDerivAt_li2Series_neg hx0 hx1
  have hneg_comp := hneg_base.comp x hneg_inner
  have hneg :
      HasDerivAt (fun t : ℝ => li2Series (-t))
        (-Real.log (1 + x) / x) x := by
    convert hneg_comp using 1 <;> field_simp [hx0.ne'] <;> ring

  have hadd : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
  have hlog_base : HasDerivAt Real.log (1 / (1 + x)) (1 + x) := by
    simpa using Real.hasDerivAt_log hden
  have hlog := hlog_base.comp x hadd
  have hlogsq :
      HasDerivAt (fun t : ℝ => (Real.log (1 + t)) ^ 2 / 2)
        (Real.log (1 + x) / (1 + x)) x := by
    convert (hlog.pow 2).div_const 2 using 1 <;> field_simp [hden] <;> ring

  have hsum := (hpos.add hneg).add hlogsq
  have hcoef :
      Real.log (1 + x) / (x * (1 + x)) +
          (-Real.log (1 + x)) / x +
          Real.log (1 + x) / (1 + x) = 0 := by
    field_simp [hx0.ne', hden]
    ring
  unfold landenCombination
  convert hsum using 1
  exact hcoef.symm

end GppRegulatedBoxLandenDerivative

#print axioms GppRegulatedBoxLandenDerivative.landenCombination_hasDerivAt_zero
