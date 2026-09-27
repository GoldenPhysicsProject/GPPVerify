import GppVerify.CelestialHolography.ContinuousSechLevyKernel

/-!
# Continuous sech Lévy frequency-derivative kernel

For the compensated kernel

  K_c(t,x) = (1 - cos(t x)) nu_c(x),

the formal pointwise derivative with respect to the frequency parameter is

  D_c(t,x) = x sin(t x) nu_c(x).

This file records the exact algebraic structure of that derivative kernel.  It
is deliberately independent of differentiation under the integral sign; the
latter requires a parameter-uniform integrable majorant and is a separate
analytic theorem.
-/

namespace GppContinuousSechLevyFrequencyDerivative

open GppContinuousSechLevyKernel

/-- Pointwise frequency-derivative kernel associated with the compensated Lévy kernel. -/
noncomputable def frequencyDerivativeKernel (c t x : ℝ) : ℝ :=
  x * Real.sin (t * x) * levyDensity c x

/-- The derivative kernel is exactly additive in the chamber parameter. -/
theorem frequencyDerivativeKernel_add (c d t x : ℝ) :
    frequencyDerivativeKernel (c + d) t x =
      frequencyDerivativeKernel c t x + frequencyDerivativeKernel d t x := by
  unfold frequencyDerivativeKernel
  rw [levyDensity_add]
  ring

/-- Frequency reflection changes the sign of the derivative kernel. -/
theorem frequencyDerivativeKernel_neg_frequency (c t x : ℝ) :
    frequencyDerivativeKernel c (-t) x = -frequencyDerivativeKernel c t x := by
  unfold frequencyDerivativeKernel
  rw [show (-t) * x = -(t * x) by ring, Real.sin_neg]
  ring

/-- Spatial reflection leaves the derivative kernel unchanged. -/
theorem frequencyDerivativeKernel_neg_space (c t x : ℝ) :
    frequencyDerivativeKernel c t (-x) = frequencyDerivativeKernel c t x := by
  unfold frequencyDerivativeKernel
  rw [levyDensity_neg]
  rw [show t * (-x) = -(t * x) by ring, Real.sin_neg]
  ring

/-- The derivative kernel vanishes at zero frequency. -/
theorem frequencyDerivativeKernel_zero_frequency (c x : ℝ) :
    frequencyDerivativeKernel c 0 x = 0 := by
  simp [frequencyDerivativeKernel]

/-- The derivative kernel vanishes at the spatial origin. -/
theorem frequencyDerivativeKernel_at_zero (c t : ℝ) :
    frequencyDerivativeKernel c t 0 = 0 := by
  simp [frequencyDerivativeKernel, levyDensity_at_zero]

end GppContinuousSechLevyFrequencyDerivative

#print axioms GppContinuousSechLevyFrequencyDerivative.frequencyDerivativeKernel_add
#print axioms GppContinuousSechLevyFrequencyDerivative.frequencyDerivativeKernel_neg_frequency
#print axioms GppContinuousSechLevyFrequencyDerivative.frequencyDerivativeKernel_neg_space
#print axioms GppContinuousSechLevyFrequencyDerivative.frequencyDerivativeKernel_zero_frequency
#print axioms GppContinuousSechLevyFrequencyDerivative.frequencyDerivativeKernel_at_zero
