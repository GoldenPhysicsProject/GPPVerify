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

  have hnum : HasDerivAt (fun t : ℝ => -t) (-1) y := by
    simpa using (hasDerivAt_id y).neg
  have hdenfun : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := by
    convert (hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y) using 1 <;> ring
  have hinner_raw := hnum.div hdenfun hden
  have hinner :
      HasDerivAt (fun t : ℝ => (-t) / (1 - t)) (-1 / (1 - y) ^ 2) y := by
    convert hinner_raw using 1 <;> field_simp [hden] <;> ring

  have hLiBase := GppRegulatedBoxDilogDerivative.hasDerivAt_li2Series ha0 ha1
  have hLiComp := hLiBase.comp y hinner

  have hone_minus : 1 - a = 1 / (1 - y) := by
    dsimp [a]
    field_simp [hden]
  have hrecipne : (1 / (1 - y) : ℝ) ≠ 0 := one_div_ne_zero hden
  have hlogrecip : Real.log (1 / (1 - y)) = -Real.log (1 - y) := by
    have hm := Real.log_mul hrecipne hden
    have hmul : (1 / (1 - y)) * (1 - y) = (1 : ℝ) := by
      field_simp [hden]
    rw [hmul, Real.log_one] at hm
    linarith
  have hLi :
      HasDerivAt (fun t : ℝ => -li2Series ((-t) / (1 - t)))
        (-Real.log (1 - y) / (y * (1 - y))) y := by
    rw [hone_minus, hlogrecip] at hLiComp
    have H := hLiComp.neg
    dsimp [a] at H
    convert H using 1 <;> field_simp [hyne, hden] <;> ring

  have hlogBase : HasDerivAt Real.log (1 / (1 - y)) (1 - y) := by
    simpa using Real.hasDerivAt_log hden
  have hlogComp := hlogBase.comp y hdenfun
  have hlogSq :
      HasDerivAt (fun t : ℝ => -((Real.log (1 - t)) ^ 2 / 2))
        (Real.log (1 - y) / (1 - y)) y := by
    have H := (hlogComp.pow 2).div_const 2
    have Hneg := H.neg
    convert Hneg using 1 <;> field_simp [hden] <;> ring

  unfold li2NegativeExtension
  have H := hLi.add hlogSq
  convert H using 1 <;> field_simp [hyne, hden] <;> ring

end GppRegulatedBoxDilogNegativeExtension

#print axioms GppRegulatedBoxDilogNegativeExtension.li2NegativeExtension_eq_series_neg
#print axioms GppRegulatedBoxDilogNegativeExtension.hasDerivAt_li2NegativeExtension
