import GppVerify.CelestialHolography.RaisedBoxInnerDCT
import GppVerify.CelestialHolography.RaisedBoxRealMajorantSliceIntegral
import GppVerify.CelestialHolography.RaisedBoxRealMajorantMiddleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Raised-box middle DCT preparation

After the innermost `x3` dominated-convergence step, the next variable is `x2`.
The exact integrated singular majorant is useful, but the middle DCT does not
need to carry its full affine dependence.  On a physical simplex slice
`0 ≤ L ≤ 1` and for `0 < δ < 1`,

  ∫₀ᴸ [1 + (S x1 x3)^(-δ)] dx3
    ≤ 1 + (S x1)^(-δ)/(1-δ).

The right-hand side is constant in `x2`.  This file packages that simpler
DCT-ready bound and the pointwise middle-slice limit.  It does not yet claim
the full `x2` dominated-convergence theorem or the three-simplex limit.
-/

namespace GppRaisedBoxMiddleDCTPrep

open MeasureTheory Filter Real
open scoped Interval Topology
open GppRaisedBoxConcreteMoment
open GppRaisedBoxInnerDCT
open GppRaisedBoxRealMajorantSliceIntegral
open GppRaisedBoxRealMajorantMiddleIntegral

/-- A simple `x2`-constant majorant for the already integrated `x3` slice. -/
noncomputable def middleMajorant (δ S x1 : ℝ) : ℝ :=
  1 + (S * x1) ^ (-δ : ℝ) / (1 - δ)

/-- The middle majorant is nonnegative in the physical regulator range. -/
theorem middleMajorant_nonneg
    {δ S x1 : ℝ} (hδ : δ < 1) (hS : 0 ≤ S) (hx1 : 0 ≤ x1) :
    0 ≤ middleMajorant δ S x1 := by
  unfold middleMajorant
  have hpow : 0 ≤ (S * x1) ^ (-δ : ℝ) :=
    Real.rpow_nonneg (mul_nonneg hS hx1) (-δ)
  have hden : 0 < 1 - δ := sub_pos.mpr hδ
  positivity

/-- Being constant in `x2`, the simplified middle majorant is interval-integrable
on every affine middle slice. -/
theorem middleMajorant_intervalIntegrable
    (δ S x1 A B : ℝ) :
    IntervalIntegrable (fun _x2 : ℝ => middleMajorant δ S x1) volume A B :=
  intervalIntegrable_const

/-- Exact integral of the innermost one-channel majorant. -/
theorem inner_majorant_integral_eq
    {δ S x1 L : ℝ}
    (hδ : δ < 1) (hS : 0 ≤ S) (hx1 : 0 ≤ x1) (hL : 0 ≤ L) :
    (∫ x3 : ℝ in 0..L, 1 + (S * x1 * x3) ^ (-δ : ℝ)) =
      L + (S * x1) ^ (-δ : ℝ) *
        (L ^ (1 - δ : ℝ) / (1 - δ)) := by
  have hconst : IntervalIntegrable (fun _x3 : ℝ => (1 : ℝ)) volume 0 L :=
    intervalIntegrable_const
  have hchan :=
    GppRaisedBoxRealMajorantSlice.channel_inner_intervalIntegrable hδ hS hx1 hL
  rw [intervalIntegral.integral_add hconst hchan]
  rw [intervalIntegral.integral_const]
  rw [integral_channel_zero_to hδ hS hx1 hL]
  ring

/-- On a physical slice `0 ≤ L ≤ 1`, the exact integrated `x3` majorant is
bounded by the `x2`-constant middle majorant. -/
theorem inner_majorant_integral_le_middleMajorant
    {δ S x1 L : ℝ}
    (hδ : δ < 1) (hS : 0 ≤ S) (hx1 : 0 ≤ x1)
    (hL0 : 0 ≤ L) (hL1 : L ≤ 1) :
    (∫ x3 : ℝ in 0..L, 1 + (S * x1 * x3) ^ (-δ : ℝ)) ≤
      middleMajorant δ S x1 := by
  rw [inner_majorant_integral_eq hδ hS hx1 hL0]
  have hden : 0 < 1 - δ := sub_pos.mpr hδ
  have hexp : 0 ≤ 1 - δ := hden.le
  have hpow : L ^ (1 - δ : ℝ) ≤ 1 := by
    exact Real.rpow_le_one hL0 hL1 hexp
  have hquot : L ^ (1 - δ : ℝ) / (1 - δ) ≤ 1 / (1 - δ) :=
    (div_le_div_iff_of_pos_right hden).2 hpow
  have hscale : 0 ≤ (S * x1) ^ (-δ : ℝ) :=
    Real.rpow_nonneg (mul_nonneg hS hx1) (-δ)
  have hscaled := mul_le_mul_of_nonneg_left hquot hscale
  unfold middleMajorant
  calc
    L + (S * x1) ^ (-δ : ℝ) * (L ^ (1 - δ : ℝ) / (1 - δ)) ≤
        1 + (S * x1) ^ (-δ : ℝ) * (1 / (1 - δ)) :=
      add_le_add hL1 hscaled
    _ = 1 + (S * x1) ^ (-δ : ℝ) / (1 - δ) := by
      rw [div_eq_mul_inv, one_div]

/-- The physical inner integral itself is bounded in norm by the same simple
middle majorant whenever `0 ≤ ε ≤ δ < 1`. -/
theorem inner_integral_norm_le_middleMajorant
    {ε δ S T x1 x2 L : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2)
    (hLdef : L = 1 - x1 - x2) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ) :
    ‖∫ x3 : ℝ in 0..L, integrand ε S T x1 x2 x3‖ ≤
      middleMajorant δ S x1 := by
  have hbound : IntervalIntegrable
      (fun x3 : ℝ => 1 + (S * x1 * x3) ^ (-δ : ℝ)) volume 0 L :=
    inner_majorant_intervalIntegrable hδ1 hS.le hx1.le hL0
  have hdom :
      ∀ᵐ x3 : ℝ ∂volume.restrict (Ι (0 : ℝ) L),
        ‖integrand ε S T x1 x2 x3‖ ≤
          1 + (S * x1 * x3) ^ (-δ : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with x3 hx3
    exact inner_integrand_norm_le_majorant
      hS hT hx1 hx2 hLdef hL0 hx3 hε0 hεδ hδ0
  have hnorm := intervalIntegral.norm_integral_le_abs_of_norm_le hdom hbound
  have heq := inner_majorant_integral_eq hδ1 hS.le hx1.le hL0
  rw [heq] at hnorm
  have hpow0 : 0 ≤ L ^ (1 - δ : ℝ) := Real.rpow_nonneg hL0 (1 - δ)
  have hscale : 0 ≤ (S * x1) ^ (-δ : ℝ) :=
    Real.rpow_nonneg (mul_nonneg hS.le hx1.le) (-δ)
  have hden : 0 < 1 - δ := sub_pos.mpr hδ1
  have hmaj0 :
      0 ≤ L + (S * x1) ^ (-δ : ℝ) *
        (L ^ (1 - δ : ℝ) / (1 - δ)) := by
    positivity
  rw [abs_of_nonneg hmaj0] at hnorm
  have hupper := inner_majorant_integral_le_middleMajorant
    hδ1 hS.le hx1.le hL0 hL1
  rw [heq] at hupper
  exact hnorm.trans hupper

/-- Pointwise `x2`-slice convergence inherited from the completed inner DCT.
For fixed physical `x1,x2`, the inner integral tends to its affine length. -/
theorem inner_slice_tendsto_affine_length
    {δ S T x1 x2 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2)
    (hxsum : x1 + x2 ≤ 1) :
    Tendsto
      (fun ε : ℝ =>
        ∫ x3 in (0 : ℝ)..(1 - x1 - x2), integrand ε S T x1 x2 x3)
      (𝓝[>] 0) (𝓝 (1 - x1 - x2)) := by
  apply inner_integral_tendsto_slice_length hδ0 hδ1 hS hT hx1 hx2 rfl
  linarith

/-- Exact integral of the pointwise middle-DCT limit.  Once the `x2` DCT is
assembled, this is the value to which the double inner slice must converge. -/
theorem affine_middle_limit_integral (x1 : ℝ) :
    (∫ x2 : ℝ in (0 : ℝ)..(1 - x1), 1 - x1 - x2) =
      (1 - x1) ^ 2 / 2 := by
  have h := integral_affine_post_inner (δ := (0 : ℝ)) (L := 1 - x1) (by norm_num)
  simpa [Real.rpow_one, Real.rpow_two] using h

end GppRaisedBoxMiddleDCTPrep

#print axioms GppRaisedBoxMiddleDCTPrep.middleMajorant_nonneg
#print axioms GppRaisedBoxMiddleDCTPrep.inner_majorant_integral_eq
#print axioms GppRaisedBoxMiddleDCTPrep.inner_majorant_integral_le_middleMajorant
#print axioms GppRaisedBoxMiddleDCTPrep.inner_integral_norm_le_middleMajorant
#print axioms GppRaisedBoxMiddleDCTPrep.inner_slice_tendsto_affine_length
#print axioms GppRaisedBoxMiddleDCTPrep.affine_middle_limit_integral
