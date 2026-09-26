import GppVerify.CelestialHolography.SechConvolutionEndpoints
import Mathlib.Tactic

/-!
# Exact shifted-sech self-convolution

The scaled whole-line identity is already proved in `SechConvolutionEndpoints`:

  ∫_R pi*sinh(pi*lambda) /
      (cosh(pi*x) cosh(pi*(lambda-x))) dx = 2*pi*lambda.

Away from `lambda = 0`, the fixed nonzero factor `pi*sinh(pi*lambda)` may be
pulled through the Bochner integral and cancelled.  This file records the exact
unscaled convolution used by the Mehler--Fock / spectral-weight normalization.
-/

namespace GppSechConvolutionClosedForm

open MeasureTheory
open GppSechConvolutionEndpoints

/-- The hyperbolic sine factor is nonzero whenever the shift is nonzero. -/
theorem sinh_pi_mul_ne_zero {lam : ℝ} (hlam : lam ≠ 0) :
    Real.sinh (Real.pi * lam) ≠ 0 := by
  rcases lt_or_gt_of_ne hlam with hneg | hpos
  · exact (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg Real.pi_pos hneg)).ne
  · exact (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hpos)).ne'

/-- **Exact shifted-sech self-convolution for nonzero shift.** -/
theorem integral_sech_convolution_eq
    {lam : ℝ} (hlam : lam ≠ 0) :
    (∫ x : ℝ,
      1 / (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x)))) =
      2 * lam / Real.sinh (Real.pi * lam) := by
  let f : ℝ → ℝ := fun x =>
    1 / (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x)))
  let c : ℝ := Real.pi * Real.sinh (Real.pi * lam)
  have hsinh : Real.sinh (Real.pi * lam) ≠ 0 := sinh_pi_mul_ne_zero hlam
  have hc : c ≠ 0 := by
    exact mul_ne_zero Real.pi_ne_zero hsinh
  have hscaled := integral_scaled_sech_kernel_eq_two_pi_mul lam
  have hfactor :
      (∫ x : ℝ, c * f x) = c * (∫ x : ℝ, f x) := by
    simpa [smul_eq_mul] using (MeasureTheory.integral_smul c f)
  have hscaled' : c * (∫ x : ℝ, f x) = 2 * Real.pi * lam := by
    rw [← hfactor]
    simpa [c, f, div_eq_mul_inv, mul_assoc] using hscaled
  have hcancelpi :
      Real.sinh (Real.pi * lam) * (∫ x : ℝ, f x) = 2 * lam := by
    apply mul_left_cancel₀ Real.pi_ne_zero
    calc
      Real.pi * (Real.sinh (Real.pi * lam) * (∫ x : ℝ, f x)) =
          c * (∫ x : ℝ, f x) := by simp [c, mul_assoc]
      _ = 2 * Real.pi * lam := hscaled'
      _ = Real.pi * (2 * lam) := by ring
  apply (eq_div_iff hsinh).2
  dsimp [f] at hcancelpi ⊢
  simpa [mul_comm] using hcancelpi

end GppSechConvolutionClosedForm

#print axioms GppSechConvolutionClosedForm.sinh_pi_mul_ne_zero
#print axioms GppSechConvolutionClosedForm.integral_sech_convolution_eq
