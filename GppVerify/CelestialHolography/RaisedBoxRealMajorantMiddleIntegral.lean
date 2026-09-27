import GppVerify.CelestialHolography.RaisedBoxRealMajorantSliceIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Raised-box real majorant: exact middle affine integral

After the singular `x3` channel is integrated, the remaining affine factor on an
`x2` slice is `(L - x2)^(1-δ)`.  This file evaluates that integral exactly.
It is the second real-valued step in the nested dominated-convergence majorant.
-/

namespace GppRaisedBoxRealMajorantMiddleIntegral

open MeasureTheory Real
open scoped Interval

/-- Reversing an affine interval and integrating the post-`x3` power gives the
expected second denominator.  The hypothesis `δ < 2` is sharp for this one
endpoint integral; the physical majorant later uses the stronger `δ < 1`. -/
theorem integral_affine_post_inner
    {δ L : ℝ} (hδ : δ < 2) :
    (∫ x in (0 : ℝ)..L, (L - x) ^ (1 - δ : ℝ)) =
      L ^ (2 - δ : ℝ) / (2 - δ) := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun y : ℝ => y ^ (1 - δ : ℝ)) L]
  simp only [sub_self, sub_zero]
  have hr : -1 < 1 - δ := by linarith
  rw [integral_rpow (Or.inl hr)]
  have hp : 0 < 2 - δ := sub_pos.mpr hδ
  have hexp : 1 - δ + 1 = 2 - δ := by ring
  rw [hexp]
  simp [Real.zero_rpow hp.ne']

/-- Physical-range specialization used by the raised-box majorant. -/
theorem integral_affine_post_inner_of_delta_lt_one
    {δ L : ℝ} (hδ : δ < 1) :
    (∫ x in (0 : ℝ)..L, (L - x) ^ (1 - δ : ℝ)) =
      L ^ (2 - δ : ℝ) / (2 - δ) :=
  integral_affine_post_inner (by linarith)

/-- After the exact `x3` integration, the channel coefficient `(S*x1)^(-δ)`
is constant in the middle variable and therefore survives unchanged through
the `x2` integration.  This packages the singular part of the two-step
majorant into the exact form needed by the outer DCT layer. -/
theorem integral_scaled_affine_post_inner
    {δ S x1 L : ℝ} (hδ : δ < 1) :
    (∫ x in (0 : ℝ)..L,
        (S * x1) ^ (-δ : ℝ) * (L - x) ^ (1 - δ : ℝ)) =
      (S * x1) ^ (-δ : ℝ) *
        (L ^ (2 - δ : ℝ) / (2 - δ)) := by
  rw [intervalIntegral.integral_const_mul]
  rw [integral_affine_post_inner_of_delta_lt_one hδ]

end GppRaisedBoxRealMajorantMiddleIntegral

#print axioms GppRaisedBoxRealMajorantMiddleIntegral.integral_affine_post_inner
#print axioms GppRaisedBoxRealMajorantMiddleIntegral.integral_affine_post_inner_of_delta_lt_one
#print axioms GppRaisedBoxRealMajorantMiddleIntegral.integral_scaled_affine_post_inner
