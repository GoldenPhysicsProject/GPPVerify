import GppVerify.CelestialHolography.ContinuousSechLevyKernel

/-!
# Continuous sech Lévy kernel neutral elements

Small exact normal-form lemmas for the compensated kernel used in the
continuous chamber Lévy–Khintchine bridge.  These keep the later integral
proofs from repeatedly unfolding the singular density at the neutral
parameter/frequency values.
-/

namespace GppContinuousSechLevyKernel

/-- Zero chamber parameter gives the zero compensated kernel pointwise. -/
theorem compensatedLevyKernel_zero_parameter (t x : ℝ) :
    compensatedLevyKernel 0 t x = 0 := by
  simp [compensatedLevyKernel, levyDensity]

/-- Zero Fourier frequency gives the zero compensated kernel pointwise. -/
theorem compensatedLevyKernel_zero_frequency (c x : ℝ) :
    compensatedLevyKernel c 0 x = 0 := by
  simp [compensatedLevyKernel]

/-- Zero chamber parameter also annihilates the exponent-sign kernel. -/
theorem levyExponentKernel_zero_parameter (t x : ℝ) :
    levyExponentKernel 0 t x = 0 := by
  simp [levyExponentKernel, levyDensity]

/-- Zero Fourier frequency annihilates the exponent-sign kernel. -/
theorem levyExponentKernel_zero_frequency (c x : ℝ) :
    levyExponentKernel c 0 x = 0 := by
  simp [levyExponentKernel]

end GppContinuousSechLevyKernel

#print axioms GppContinuousSechLevyKernel.compensatedLevyKernel_zero_parameter
#print axioms GppContinuousSechLevyKernel.compensatedLevyKernel_zero_frequency
#print axioms GppContinuousSechLevyKernel.levyExponentKernel_zero_parameter
#print axioms GppContinuousSechLevyKernel.levyExponentKernel_zero_frequency
