import GppVerify.CelestialHolography.ContinuousSechLevyTail

/-!
# Continuous sech Lévy measurability

The compensated kernel

  K_c(t,x) = (1 - cos(t*x)) * c / (|x| * sinh(pi*|x|))

is a Borel-measurable totalized real function.  This analytic interface is needed
before the certified uniform/core and inverse-square/tail majorants can be packaged
into an actual `Integrable` theorem.

No integral identity is asserted here.
-/

namespace GppContinuousSechLevyMeasurability

open MeasureTheory
open GppContinuousSechLevyKernel

/-- The totalized candidate Lévy density is Borel measurable. -/
theorem measurable_levyDensity (c : ℝ) : Measurable (levyDensity c) := by
  unfold levyDensity
  fun_prop

/-- The compensated Lévy kernel is Borel measurable as a function of space. -/
theorem measurable_compensatedLevyKernel (c t : ℝ) :
    Measurable (fun x : ℝ => compensatedLevyKernel c t x) := by
  unfold compensatedLevyKernel
  fun_prop

/-- Hence the compensated Lévy kernel is strongly measurable for Lebesgue integration. -/
theorem aestronglyMeasurable_compensatedLevyKernel (c t : ℝ) :
    AEStronglyMeasurable (fun x : ℝ => compensatedLevyKernel c t x) :=
  (measurable_compensatedLevyKernel c t).aestronglyMeasurable

end GppContinuousSechLevyMeasurability

#print axioms GppContinuousSechLevyMeasurability.measurable_levyDensity
#print axioms GppContinuousSechLevyMeasurability.measurable_compensatedLevyKernel
#print axioms GppContinuousSechLevyMeasurability.aestronglyMeasurable_compensatedLevyKernel
