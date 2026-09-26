import GppVerify.CelestialHolography.MassiveCutRadialMu4Weight
import GppVerify.CelestialHolography.Mu2kRadialIntegral

/-!
# Exact radial moment of the D-dimensional `mu^4` cut numerator

The D-dimensional massive-scalar MHV cut carries a `mu^4` numerator.  On the fixed-radius
massive celestial shell,

  mu(r)^4 = M^4 / (16 cosh(r)^4).

The universal radial-shell theorem gives

  ∫_0^∞ tanh(r) / cosh(r)^4 dr = 1/4.

Combining the two yields the exact physical radial moment

  ∫_0^∞ tanh(r) mu(r)^4 dr = M^4 / 64.

This is a radial phase-space normalization statement only.  It does not supply color factors,
full D-dimensional gluon state sums, integral-reduction subtraction, or the complete one-loop
Yang--Mills amplitude.
-/

namespace GppMassiveCutMu4RadialMoment

open MeasureTheory
open GppMassiveCutRadialMu4Weight
open GppMu2kRadial

/-- The universal `mu^4` shell is the `k=1` member of the `mu^(2r)` hierarchy. -/
theorem integral_mu4_shell :
    ∫ r in Set.Ioi (0 : ℝ), Real.tanh r / Real.cosh r ^ 4 = 1 / 4 := by
  simpa using integral_radialShell 1

/-- Pointwise conversion of the physical `mu^4` numerator into the universal radial shell. -/
theorem tanh_mul_muFromRadius_pow_four (M r : ℝ) :
    Real.tanh r * muFromRadius M r ^ 4 =
      (M ^ 4 / 16) * (Real.tanh r / Real.cosh r ^ 4) := by
  rw [muFromRadius_pow_four]
  have hc : Real.cosh r ≠ 0 := ne_of_gt (Real.cosh_pos r)
  field_simp [hc]
  ring

/-- Exact fixed-radius celestial moment of the D-dimensional `mu^4` numerator. -/
theorem integral_tanh_muFromRadius_pow_four (M : ℝ) :
    ∫ r in Set.Ioi (0 : ℝ), Real.tanh r * muFromRadius M r ^ 4 = M ^ 4 / 64 := by
  calc
    ∫ r in Set.Ioi (0 : ℝ), Real.tanh r * muFromRadius M r ^ 4 =
        ∫ r in Set.Ioi (0 : ℝ), (M ^ 4 / 16) *
          (Real.tanh r / Real.cosh r ^ 4) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with r
      exact tanh_mul_muFromRadius_pow_four M r
    _ = (M ^ 4 / 16) *
        (∫ r in Set.Ioi (0 : ℝ), Real.tanh r / Real.cosh r ^ 4) := by
      rw [MeasureTheory.integral_const_mul]
    _ = M ^ 4 / 64 := by
      rw [integral_mu4_shell]
      ring

end GppMassiveCutMu4RadialMoment

#print axioms GppMassiveCutMu4RadialMoment.integral_mu4_shell
#print axioms GppMassiveCutMu4RadialMoment.integral_tanh_muFromRadius_pow_four
