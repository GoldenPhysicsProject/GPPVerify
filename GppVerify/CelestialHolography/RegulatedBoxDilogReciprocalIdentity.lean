import GppVerify.CelestialHolography.RegulatedBoxDilogInversionKernel
import GppVerify.CelestialHolography.RegulatedBoxDilogNegativeExtension
import GppVerify.CelestialHolography.RegulatedBoxDilogNegativeOneValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Branch-free reciprocal identity on the full positive axis

The Landen-defined negative-axis extension has the classical derivative at every
negative real argument.  Therefore the already-formalized reciprocal combination

  L(-x) + L(-1/x) + (1/2) log(x)^2

has derivative zero for every `x > 0`.  Convexity of `(0,∞)` makes it constant, and
its value at `x = 1` is fixed by `Li2(-1) = -pi^2/12`.
-/

namespace GppRegulatedBoxDilogReciprocalIdentity

open Set
open GppRegulatedBoxDilogSeries
open GppRegulatedBoxDilogInversionKernel
open GppRegulatedBoxDilogNegativeExtension
open GppRegulatedBoxDilogNegativeOneValue

/-- The Landen extension agrees with the certified negative endpoint value at `-1`. -/
theorem li2NegativeExtension_neg_one :
    li2NegativeExtension (-1) = -(Real.pi ^ 2) / 12 := by
  have hL := landen_at_one_endpoint
  have hN := li2Series_neg_one
  unfold li2NegativeExtension
  norm_num
  linarith [hL, hN]

/-- The reciprocal combination for the Landen extension has zero derivative on `(0,∞)`. -/
theorem inversionCombination_extension_hasDerivAt_zero
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (inversionCombination li2NegativeExtension) 0 x := by
  exact inversionCombination_hasDerivAt_zero li2NegativeExtension hx
    (fun y hy => hasDerivAt_li2NegativeExtension hy)

/-- The reciprocal combination is constant on the positive real axis. -/
theorem inversionCombination_extension_eq_on_Ioi
    {x y : ℝ} (hx : x ∈ Ioi (0 : ℝ)) (hy : y ∈ Ioi (0 : ℝ)) :
    inversionCombination li2NegativeExtension x =
      inversionCombination li2NegativeExtension y := by
  apply (convex_Ioi (0 : ℝ)).is_const_of_fderivWithin_eq_zero (𝕜 := ℝ)
  · intro z hz
    exact (inversionCombination_extension_hasDerivAt_zero hz).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [fderivWithin_of_isOpen isOpen_Ioi hz]
    rw [(inversionCombination_extension_hasDerivAt_zero hz).hasFDerivAt.fderiv]
    ext v
    simp
  · exact hx
  · exact hy

/-- The constant reciprocal combination is exactly `-pi^2/6`. -/
theorem inversionCombination_extension_eq_neg_pi_sq_div_six
    {x : ℝ} (hx : 0 < x) :
    inversionCombination li2NegativeExtension x = -(Real.pi ^ 2) / 6 := by
  have hc := inversionCombination_extension_eq_on_Ioi
    (x := x) (y := (1 : ℝ)) hx (by norm_num)
  have hneg := li2NegativeExtension_neg_one
  calc
    inversionCombination li2NegativeExtension x =
        inversionCombination li2NegativeExtension (1 : ℝ) := hc
    _ = -(Real.pi ^ 2) / 6 := by
      unfold inversionCombination
      norm_num
      rw [hneg]
      ring

/-- **Branch-free real reciprocal dilogarithm identity.** -/
theorem li2NegativeExtension_reciprocal
    {x : ℝ} (hx : 0 < x) :
    li2NegativeExtension (-x) + li2NegativeExtension (-1 / x) =
      -(Real.pi ^ 2) / 6 - (Real.log x) ^ 2 / 2 := by
  have h := inversionCombination_extension_eq_neg_pi_sq_div_six hx
  unfold inversionCombination at h
  linarith

end GppRegulatedBoxDilogReciprocalIdentity

#print axioms GppRegulatedBoxDilogReciprocalIdentity.li2NegativeExtension_neg_one
#print axioms GppRegulatedBoxDilogReciprocalIdentity.inversionCombination_extension_hasDerivAt_zero
#print axioms GppRegulatedBoxDilogReciprocalIdentity.inversionCombination_extension_eq_on_Ioi
#print axioms GppRegulatedBoxDilogReciprocalIdentity.inversionCombination_extension_eq_neg_pi_sq_div_six
#print axioms GppRegulatedBoxDilogReciprocalIdentity.li2NegativeExtension_reciprocal
