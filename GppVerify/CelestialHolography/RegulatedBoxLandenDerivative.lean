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

  have hinner :
      HasDerivAt (fun t : ℝ => t / (1 + t)) (1 / (1 + x) ^ 2) x := by
    have h := (hasDerivAt_id x).fun_div
      ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)) hden
    refine h.congr_deriv ?_
    simp only [id, Pi.add_apply]
    ring

  have hpos_base := hasDerivAt_li2Series hy0 hy1
  have hpos_comp := hpos_base.comp x hinner

  have hone_minus : 1 - x / (1 + x) = (1 + x)⁻¹ := by
    rw [one_sub_div hden, add_sub_cancel_right, one_div]
  have hpos :
      HasDerivAt (fun t : ℝ => li2Series (t / (1 + t)))
        (Real.log (1 + x) / (x * (1 + x))) x := by
    refine hpos_comp.congr_deriv ?_
    rw [hone_minus, Real.log_inv]
    field_simp

  have hneg_inner : HasDerivAt (fun t : ℝ => -t) (-1) x := (hasDerivAt_id x).neg
  have hneg_base := hasDerivAt_li2Series_neg hx0 hx1
  have hneg_comp := hneg_base.comp x hneg_inner
  have hneg :
      HasDerivAt (fun t : ℝ => li2Series (-t))
        (-Real.log (1 + x) / x) x := by
    refine hneg_comp.congr_deriv ?_
    field_simp

  have hadd : HasDerivAt (fun t : ℝ => 1 + t) 1 x :=
    ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).congr_deriv (zero_add _)
  have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + x)) x :=
    ((Real.hasDerivAt_log hden).comp x hadd).congr_deriv (by rw [mul_one, one_div])
  have hlogsq :
      HasDerivAt (fun t : ℝ => (Real.log (1 + t)) ^ 2 / 2)
        (Real.log (1 + x) / (1 + x)) x := by
    refine ((hlog.pow 2).div_const 2).congr_deriv ?_
    norm_num <;> ring

  have hsum := (hpos.add hneg).add hlogsq
  have hcoef :
      Real.log (1 + x) / (x * (1 + x)) +
          (-Real.log (1 + x)) / x +
          Real.log (1 + x) / (1 + x) = 0 := by
    field_simp
    ring
  unfold landenCombination
  exact hsum.congr_deriv hcoef

end GppRegulatedBoxLandenDerivative

#print axioms GppRegulatedBoxLandenDerivative.landenCombination_hasDerivAt_zero
