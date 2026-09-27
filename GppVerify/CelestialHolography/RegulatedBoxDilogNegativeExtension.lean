import GppVerify.CelestialHolography.RegulatedBoxDilogDerivativeUnitDisk
import GppVerify.CelestialHolography.RegulatedBoxLandenIdentity
import Mathlib.Tactic

/-!
# Branch-free extension of the real dilogarithm to the negative axis

For `y < 0`, set

  Li₂⁻(y) = -Li₂(-y/(1-y)) - 1/2 log(1-y)^2.

The transformed argument lies in `(0,1)`, so the right-hand side uses only the already
certified real power-series dilogarithm.  Landen identifies this extension with the
series on `(-1,0)`, while direct differentiation gives the standard real derivative
`-log(1-y)/y` on the whole negative axis.
-/

namespace GppRegulatedBoxDilogNegativeExtension

open GppRegulatedBoxDilogSeries
open GppRegulatedBoxDilogDerivative
open GppRegulatedBoxDilogDerivativeUnitDisk
open GppRegulatedBoxLandenIdentity

/-- Branch-free real dilogarithm extension on the negative axis. -/
noncomputable def li2NegativeExtension (y : ℝ) : ℝ :=
  -li2Series ((-y) / (1 - y)) - (Real.log (1 - y)) ^ 2 / 2

/-- The Landen-transformed argument of a negative real number lies in `(0,1)`. -/
theorem neg_div_one_sub_mem_Ioo {y : ℝ} (hy : y < 0) :
    0 < (-y) / (1 - y) ∧ (-y) / (1 - y) < 1 := by
  have hden : 0 < 1 - y := by linarith
  constructor
  · exact div_pos (by linarith) hden
  · apply (div_lt_one hden).2
    linarith

/-- On `(-1,0)`, the branch-free extension agrees with the original real series. -/
theorem li2NegativeExtension_eq_series_neg
    {y : ℝ} (hyneg : -1 < y) (hy0 : y < 0) :
    li2NegativeExtension y = li2Series y := by
  have hx0 : 0 < -y := by linarith
  have hx1 : -y < 1 := by linarith
  have hL := li2Series_landen hx0 hx1
  have hnegneg : -(-y) = y := by ring
  have hone : 1 + (-y) = 1 - y := by ring
  rw [hnegneg, hone] at hL
  dsimp [li2NegativeExtension]
  linarith

/-- The branch-free negative-axis extension has the expected derivative. -/
theorem hasDerivAt_li2NegativeExtension
    {y : ℝ} (hy : y < 0) :
    HasDerivAt li2NegativeExtension (-Real.log (1 - y) / y) y := by
  have hdenpos : 0 < 1 - y := by linarith
  have hden : 1 - y ≠ 0 := hdenpos.ne'
  have hyne : y ≠ 0 := ne_of_lt hy
  let a : ℝ := (-y) / (1 - y)
  have ha := neg_div_one_sub_mem_Ioo hy
  have ha0 : 0 < a := by simpa [a] using ha.1
  have ha1 : a < 1 := by simpa [a] using ha.2

  have hnum : HasDerivAt (fun t : ℝ => -t) (-1) y := (hasDerivAt_id y).neg
  have hdenfun : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := (hasDerivAt_id y).const_sub 1
  have hinner :
      HasDerivAt (fun t : ℝ => (-t) / (1 - t)) (-1 / (1 - y) ^ 2) y := by
    refine (hnum.fun_div hdenfun hden).congr_deriv ?_
    ring

  have hLiBase := GppRegulatedBoxDilogDerivative.hasDerivAt_li2Series ha0 ha1
  have hLiComp := hLiBase.comp y hinner

  have hone_minus : 1 - a = 1 / (1 - y) := by
    dsimp [a]
    field_simp
    ring
  have hlogrecip : Real.log (1 / (1 - y)) = -Real.log (1 - y) := by
    rw [one_div, Real.log_inv]
  have hLi :
      HasDerivAt (fun t : ℝ => -li2Series ((-t) / (1 - t)))
        (-Real.log (1 - y) / (y * (1 - y))) y := by
    rw [hone_minus, hlogrecip] at hLiComp
    refine hLiComp.neg.congr_deriv ?_
    dsimp [a]
    field_simp

  have hlogComp := (Real.hasDerivAt_log hden).comp y hdenfun
  have hlogSq :
      HasDerivAt (fun t : ℝ => -((Real.log (1 - t)) ^ 2 / 2))
        (Real.log (1 - y) / (1 - y)) y := by
    refine ((hlogComp.pow 2).div_const 2).neg.congr_deriv ?_
    simp only [Function.comp_apply, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp
    ring

  unfold li2NegativeExtension
  refine ((hLi.add hlogSq).congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => ?_)
  · field_simp
    ring
  · simp only [Pi.add_apply]
    ring

end GppRegulatedBoxDilogNegativeExtension

#print axioms GppRegulatedBoxDilogNegativeExtension.li2NegativeExtension_eq_series_neg
#print axioms GppRegulatedBoxDilogNegativeExtension.hasDerivAt_li2NegativeExtension
