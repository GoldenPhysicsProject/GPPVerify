import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# Elementary kernel behind the sech self-convolution

This is the pointwise hyperbolic identity used in the Discovery2 elementary proof of
`sech(pi * ·) * sech(pi * ·)` convolution.  The improper integral and endpoint limits
are intentionally left for the next layer.
-/

namespace GppSechConvolutionKernel

/-- Addition-law form of the product of two reciprocal coshes. -/
theorem reciprocal_cosh_product_identity
    (A B : ℝ)
    (hA : Real.cosh A ≠ 0)
    (hB : Real.cosh B ≠ 0) :
    Real.sinh A / Real.cosh A + Real.sinh B / Real.cosh B =
      Real.sinh (A + B) / (Real.cosh A * Real.cosh B) := by
  rw [Real.sinh_add]
  field_simp [hA, hB]
  ring

/-- Solved form of the same identity, ready for integration: the reciprocal-cosh
product is a tanh sum divided by the total-channel `sinh`. -/
theorem reciprocal_cosh_product_eq_tanh_sum_div
    (A B : ℝ)
    (hA : Real.cosh A ≠ 0)
    (hB : Real.cosh B ≠ 0)
    (hAB : Real.sinh (A + B) ≠ 0) :
    1 / (Real.cosh A * Real.cosh B) =
      (Real.sinh A / Real.cosh A + Real.sinh B / Real.cosh B) /
        Real.sinh (A + B) := by
  have h := reciprocal_cosh_product_identity A B hA hB
  rw [h]
  field_simp [hAB]

/-- Specialized kernel identity for `A = pi*x`, `B = pi*(lambda-x)`.
It is the algebraic heart of the elementary self-convolution proof. -/
theorem pi_shift_kernel_identity
    (x lam : ℝ)
    (hx : Real.cosh (Real.pi * x) ≠ 0)
    (hshift : Real.cosh (Real.pi * (lam - x)) ≠ 0) :
    Real.sinh (Real.pi * x) / Real.cosh (Real.pi * x) +
      Real.sinh (Real.pi * (lam - x)) / Real.cosh (Real.pi * (lam - x)) =
      Real.sinh (Real.pi * lam) /
        (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x))) := by
  have h := reciprocal_cosh_product_identity
    (Real.pi * x) (Real.pi * (lam - x)) hx hshift
  convert h using 1 <;> ring

/-- Derivative-ready specialized solved form.  For `lambda != 0`, the convolution
integrand is exactly a sum of two tanh kernels divided by `sinh(pi*lambda)`. -/
theorem pi_shift_reciprocal_product_eq_tanh_sum_div
    (x lam : ℝ) (hlam : lam ≠ 0) :
    1 / (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x))) =
      (Real.sinh (Real.pi * x) / Real.cosh (Real.pi * x) +
        Real.sinh (Real.pi * (lam - x)) / Real.cosh (Real.pi * (lam - x))) /
        Real.sinh (Real.pi * lam) := by
  have hx : Real.cosh (Real.pi * x) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hshift : Real.cosh (Real.pi * (lam - x)) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hpilam : Real.pi * lam ≠ 0 := mul_ne_zero Real.pi_ne_zero hlam
  have hsinh : Real.sinh (Real.pi * lam) ≠ 0 :=
    (Real.sinh_ne_zero).2 hpilam
  have h := reciprocal_cosh_product_eq_tanh_sum_div
    (Real.pi * x) (Real.pi * (lam - x)) hx hshift (by
      convert hsinh using 1 <;> ring)
  convert h using 1 <;> ring

end GppSechConvolutionKernel

#print axioms GppSechConvolutionKernel.reciprocal_cosh_product_identity
#print axioms GppSechConvolutionKernel.reciprocal_cosh_product_eq_tanh_sum_div
#print axioms GppSechConvolutionKernel.pi_shift_kernel_identity
#print axioms GppSechConvolutionKernel.pi_shift_reciprocal_product_eq_tanh_sum_div
