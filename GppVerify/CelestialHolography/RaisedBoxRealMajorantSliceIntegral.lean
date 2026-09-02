import GppVerify.CelestialHolography.RaisedBoxRealMajorantSlice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Raised-box real majorant: exact singular slice integral

For `δ < 1`, the endpoint singularity is not only integrable: its affine-slice
integral is explicit.  This is the real-valued counterpart needed for the
nested dominated-convergence assembly.
-/

namespace GppRaisedBoxRealMajorantSliceIntegral

open MeasureTheory Real
open scoped Interval
open GppRaisedBoxRealMajorantSlice

/-- Exact endpoint integral for the real singularity. -/
theorem integral_neg_rpow_zero_to
    {δ L : ℝ} (hδ : δ < 1) :
    (∫ x : ℝ in 0..L, x ^ (-δ : ℝ)) =
      L ^ (1 - δ : ℝ) / (1 - δ) := by
  have hr : -1 < -δ := by linarith
  rw [integral_rpow (Or.inl hr)]
  have hp : 0 < 1 - δ := sub_pos.mpr hδ
  have hexp : -δ + 1 = 1 - δ := by ring
  rw [hexp]
  simp [Real.zero_rpow hp.ne']

/-- On a nonnegative affine simplex slice, the scaled singular channel has the
explicit endpoint integral expected from homogeneity. -/
theorem integral_channel_zero_to
    {S x1 δ L : ℝ}
    (hδ : δ < 1) (hS : 0 ≤ S) (hx1 : 0 ≤ x1) (hL : 0 ≤ L) :
    (∫ x3 : ℝ in 0..L, (S * x1 * x3) ^ (-δ : ℝ)) =
      (S * x1) ^ (-δ : ℝ) * (L ^ (1 - δ : ℝ) / (1 - δ)) := by
  calc
    (∫ x3 : ℝ in 0..L, (S * x1 * x3) ^ (-δ : ℝ)) =
        ∫ x3 : ℝ in 0..L, (S * x1) ^ (-δ : ℝ) * x3 ^ (-δ : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x3 hx3
      rw [Set.uIcc_of_le hL] at hx3
      exact channel_neg_rpow_factor hS hx1 hx3.1
    _ = (S * x1) ^ (-δ : ℝ) *
        (∫ x3 : ℝ in 0..L, x3 ^ (-δ : ℝ)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (S * x1) ^ (-δ : ℝ) * (L ^ (1 - δ : ℝ) / (1 - δ)) := by
      rw [integral_neg_rpow_zero_to hδ]

end GppRaisedBoxRealMajorantSliceIntegral

#print axioms GppRaisedBoxRealMajorantSliceIntegral.integral_neg_rpow_zero_to
#print axioms GppRaisedBoxRealMajorantSliceIntegral.integral_channel_zero_to
