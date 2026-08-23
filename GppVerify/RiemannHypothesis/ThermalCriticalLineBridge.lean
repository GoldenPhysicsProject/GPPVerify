import GppVerify.NumberTheory.ZetaProperties
import GppVerify.QuantumGravity.GammaModulusIdentity
import GppVerify.QuantumGravity.StefanBoltzmannFamily
import GppVerify.RiemannHypothesis.PrimeOccupationBridge
import GppVerify.RiemannHypothesis.PrimeGasPartition
import GppVerify.RiemannHypothesis.CompletedZetaReality

/-!
# Thermal critical-line bridge

This file packages exact facts motivating a thermal interpretation of the Riemann critical line
without asserting the physical interpretation as a theorem.

1. The reflection/conjugation equilibrium locus is exactly `Re s = 1/2`.
2. The principal-series Gamma modulus is exactly the Planck spectral weight
   `P(λ) = π λ / sinh(π λ)`.
3. Mellin moments of that same `P` obey the generalized Stefan–Boltzmann Gamma-zeta law.
4. Each local prime response has the same geometric occupation denominator as a repeated-mode
   occupation law, and the infinite product of local prime partition factors is exactly zeta
   on `Re s > 1`.
5. The completed zeta function is real on the critical line because functional-equation
   reflection and complex conjugation coincide there.
6. Any response that is reflection-odd and conjugation-covariant has zero real part on the
   equilibrium locus. This is the precise algebraic form of the anti-Hermitian / zero-flux
   response condition suggested by the thermodynamic analogy.
-/

namespace GppThermalCriticalLine

open Complex
open MeasureTheory Real Set

/-- The unique locus where functional-equation reflection agrees with complex conjugation is
exactly the Riemann critical line. This is the precise involutive part of the equilibrium analogy. -/
theorem equilibrium_involution_iff_critical_line (s : ℂ) :
    starRingEnd ℂ s = 1 - s ↔ s.re = 1 / 2 :=
  GppZeta.critical_line_unique_fixed_locus s

/-- On the principal series, the Gamma modulus is exactly the Planck spectral weight. -/
theorem principalSeries_gamma_modulus_eq_planck_weight (lam : ℝ) (hlam : lam ≠ 0) :
    Complex.Gamma (1 + (lam : ℂ) * I) * Complex.Gamma (1 - (lam : ℂ) * I)
      = ((GppStefanBoltzmann.P lam : ℝ) : ℂ) := by
  simpa [GppStefanBoltzmann.P] using
    GppGammaModulus.gamma_one_add_mul_gamma_one_sub lam hlam

/-- The first thermal moment of the principal-series Planck weight is exactly `1/8`. -/
theorem planck_weight_first_moment :
    (1 / (2 * Real.pi)) *
      ∫ lam in Ioi (0 : ℝ), lam ^ ((1 : ℝ) - 1) * GppStefanBoltzmann.P lam = 1 / 8 :=
  GppStefanBoltzmann.m_one_eq

/-- The cubic thermal moment is exactly `1/16`. -/
theorem planck_weight_third_moment :
    (1 / (2 * Real.pi)) *
      ∫ lam in Ioi (0 : ℝ), lam ^ ((3 : ℝ) - 1) * GppStefanBoltzmann.P lam = 1 / 16 :=
  GppStefanBoltzmann.m_three_eq

/-- The completed partition amplitude is real on the equilibrium contour. -/
theorem completed_partition_im_zero {s : ℂ} (hs : s.re = 1 / 2) :
    (completedRiemannZeta s).im = 0 :=
  GppCompletedZetaReality.completedRiemannZeta_im_eq_zero_of_re_half hs

/-- **Equilibrium response condition.** If a complex response is odd under the functional-equation
reflection and covariant under complex conjugation, then its real part vanishes on the critical
line. In physics language this is the algebraic anti-Hermitian / zero-dissipative-flux condition. -/
theorem equilibrium_response_re_zero
    (R : ℂ → ℂ) (s : ℂ)
    (hcrit : s.re = 1 / 2)
    (hreflect : R s = -R (1 - s))
    (hconj : R (starRingEnd ℂ s) = starRingEnd ℂ (R s)) :
    (R s).re = 0 := by
  have heq : starRingEnd ℂ s = 1 - s :=
    (equilibrium_involution_iff_critical_line s).2 hcrit
  have hanti : R s = -(starRingEnd ℂ (R s)) := by
    rw [← heq] at hreflect
    rw [hconj] at hreflect
    exact hreflect
  have hre := congrArg Complex.re hanti
  simp [RCLike.star_def, Complex.conj_re] at hre
  linarith

end GppThermalCriticalLine

#print axioms GppThermalCriticalLine.equilibrium_involution_iff_critical_line
#print axioms GppThermalCriticalLine.principalSeries_gamma_modulus_eq_planck_weight
#print axioms GppThermalCriticalLine.planck_weight_first_moment
#print axioms GppThermalCriticalLine.planck_weight_third_moment
#print axioms GppThermalCriticalLine.completed_partition_im_zero
#print axioms GppThermalCriticalLine.equilibrium_response_re_zero
