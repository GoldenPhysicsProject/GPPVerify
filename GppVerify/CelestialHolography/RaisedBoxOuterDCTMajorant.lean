import GppVerify.CelestialHolography.RaisedBoxMiddleMeasurability
import GppVerify.CelestialHolography.RaisedBoxRealMajorantIntegrability
import Mathlib.Tactic

/-!
# Raised-box outer dominated-convergence majorant

The middle-coordinate DCT bounds the fixed-`x1` two-inner-coordinate integral by

  1 + (S*x1)^(-δ) / (1-δ).

For `0 < δ < 1` and `S > 0`, this is interval-integrable on `[0,1]`.  This file
packages that exact outer majorant independently of the final DCT assembly.
-/

namespace GppRaisedBoxOuterDCTMajorant

open MeasureTheory Real
open scoped Interval
open GppRaisedBoxRealMajorantIntegrability

/-- The scaled outer endpoint singularity `(S*x)^(-δ)` is interval-integrable
on the unit interval for every `S ≥ 0` and `δ < 1`. -/
theorem scaled_neg_rpow_unit_intervalIntegrable
    {δ S : ℝ} (hδ : δ < 1) (hS : 0 ≤ S) :
    IntervalIntegrable (fun x : ℝ => (S * x) ^ (-δ : ℝ)) volume 0 1 := by
  have hbase : IntervalIntegrable
      (fun x : ℝ => x ^ (-δ : ℝ)) volume 0 1 :=
    neg_rpow_unit_intervalIntegrable hδ
  have hscaled : IntervalIntegrable
      (fun x : ℝ => S ^ (-δ : ℝ) * x ^ (-δ : ℝ)) volume 0 1 :=
    hbase.const_mul (S ^ (-δ : ℝ))
  apply hscaled.congr
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hx
  exact (Real.mul_rpow hS hx.1.le).symm

/-- The explicit fixed-`x1` bound used after the middle DCT is itself
interval-integrable in the outer simplex coordinate. -/
theorem middleConstant_outer_intervalIntegrable
    {δ S : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hS : 0 < S) :
    IntervalIntegrable
      (fun x : ℝ => 1 + (S * x) ^ (-δ : ℝ) / (1 - δ))
      volume 0 1 := by
  have hsing : IntervalIntegrable
      (fun x : ℝ => (S * x) ^ (-δ : ℝ)) volume 0 1 :=
    scaled_neg_rpow_unit_intervalIntegrable hδ1 hS.le
  have hdiv : IntervalIntegrable
      (fun x : ℝ => (S * x) ^ (-δ : ℝ) / (1 - δ)) volume 0 1 := by
    simpa [div_eq_mul_inv, mul_comm] using
      hsing.const_mul ((1 - δ)⁻¹)
  exact intervalIntegrable_const.add hdiv

end GppRaisedBoxOuterDCTMajorant

#print axioms GppRaisedBoxOuterDCTMajorant.scaled_neg_rpow_unit_intervalIntegrable
#print axioms GppRaisedBoxOuterDCTMajorant.middleConstant_outer_intervalIntegrable
