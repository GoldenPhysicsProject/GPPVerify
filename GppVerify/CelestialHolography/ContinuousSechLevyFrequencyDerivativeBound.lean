import GppVerify.CelestialHolography.ContinuousSechLevyFrequencyDerivative

/-!
# Global bound for the continuous sech Lévy frequency derivative

This file isolates the pointwise estimate needed on the compact-frequency core
of the later dominated-convergence argument. The bound is global pointwise,
but it is not by itself an `L¹` tail majorant.
-/

namespace GppContinuousSechLevyFrequencyDerivativeBound

open GppContinuousSechLevyKernel
open GppContinuousSechLevyFrequencyDerivative

/-- For nonnegative chamber parameter, the absolute frequency-derivative kernel
is globally bounded by `c * |t| / pi`. -/
theorem abs_frequencyDerivativeKernel_le {c t x : ℝ} (hc : 0 ≤ c) :
    |frequencyDerivativeKernel c t x| ≤ c * |t| / Real.pi := by
  unfold frequencyDerivativeKernel
  rw [abs_mul, abs_mul]
  have hnu : 0 ≤ levyDensity c x := levyDensity_nonneg_global hc
  rw [abs_of_nonneg hnu]
  have hsin : |Real.sin (t * x)| ≤ |t * x| := Real.abs_sin_le_abs
  have hfirst :
      |x| * |Real.sin (t * x)| * levyDensity c x ≤
        |x| * |t * x| * levyDensity c x := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsin (abs_nonneg x)) hnu
  have hsq := sq_abs_mul_levyDensity_le (c := c) (x := x) hc
  have hsecond :
      |t| * (|x| ^ 2 * levyDensity c x) ≤ |t| * (c / Real.pi) :=
    mul_le_mul_of_nonneg_left hsq (abs_nonneg t)
  calc
    |x| * |Real.sin (t * x)| * levyDensity c x
        ≤ |x| * |t * x| * levyDensity c x := hfirst
    _ = |t| * (|x| ^ 2 * levyDensity c x) := by rw [abs_mul]; ring
    _ ≤ |t| * (c / Real.pi) := hsecond
    _ = c * |t| / Real.pi := by ring

end GppContinuousSechLevyFrequencyDerivativeBound

#print axioms GppContinuousSechLevyFrequencyDerivativeBound.abs_frequencyDerivativeKernel_le
