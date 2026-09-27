import GppVerify.CelestialHolography.RaisedBoxRealMajorantIntegrability
import Mathlib.Tactic

/-!
# Raised-box real majorant: affine-slice integrability

This file connects the one-variable endpoint certificate to the actual singular
channel appearing in the concrete raised-box majorant.  On a nonnegative slice,

  (S * x1 * x3)^(-δ) = (S * x1)^(-δ) * x3^(-δ),

so the inner `x3` integral is interval-integrable whenever `δ < 1`.
-/

namespace GppRaisedBoxRealMajorantSlice

open MeasureTheory Real
open scoped Interval
open GppRaisedBoxRealMajorantIntegrability

/-- Exact nonnegative real-power factorization of the singular channel. -/
theorem channel_neg_rpow_factor
    {S x1 x3 δ : ℝ}
    (hS : 0 ≤ S) (hx1 : 0 ≤ x1) (hx3 : 0 ≤ x3) :
    (S * x1 * x3) ^ (-δ : ℝ) =
      (S * x1) ^ (-δ : ℝ) * x3 ^ (-δ : ℝ) := by
  exact Real.mul_rpow (mul_nonneg hS hx1) hx3

/-- For every nonnegative affine inner simplex slice `[0,L]`, the singular
channel is interval-integrable as a function of `x3`.  The condition `0 ≤ L`
is essential: it ensures the whole interval lies in the nonnegative region
where the real-power product factorization applies. -/
theorem channel_inner_intervalIntegrable
    {S x1 δ L : ℝ}
    (hδ : δ < 1) (hS : 0 ≤ S) (hx1 : 0 ≤ x1) (hL : 0 ≤ L) :
    IntervalIntegrable
      (fun x3 : ℝ => (S * x1 * x3) ^ (-δ : ℝ)) volume 0 L := by
  have hbase : IntervalIntegrable
      (fun x3 : ℝ => x3 ^ (-δ : ℝ)) volume 0 L :=
    neg_rpow_affine_slice_intervalIntegrable hδ
  have hscaled : IntervalIntegrable
      (fun x3 : ℝ => (S * x1) ^ (-δ : ℝ) * x3 ^ (-δ : ℝ)) volume 0 L :=
    hbase.const_mul ((S * x1) ^ (-δ : ℝ))
  apply hscaled.congr
  intro x3 hx3
  rw [Set.uIoc_of_le hL] at hx3
  exact (channel_neg_rpow_factor hS hx1 hx3.1.le).symm

end GppRaisedBoxRealMajorantSlice

#print axioms GppRaisedBoxRealMajorantSlice.channel_neg_rpow_factor
#print axioms GppRaisedBoxRealMajorantSlice.channel_inner_intervalIntegrable
