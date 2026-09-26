import GppVerify.CelestialHolography.WienerHopfWeightExtension
import GppVerify.QuantumGravity.SpectralRhoMehlerFockBridge
import Mathlib.Tactic

/-!
# Exact bridge from the Wiener--Hopf weight to the normalized Gamma chamber

Two previously independent formalization threads meet exactly at the base
normalized Gamma/Mehler--Fock spectral family.

The continuously extended Wiener--Hopf weight is

  W_ext(x) = pi*x/sinh(pi*x),   x != 0,
  W_ext(0) = 1.

The base normalized Gamma chamber is

  rhoGamma(0,x) = 2*x/sinh(pi*x),   x != 0,
  rhoGamma(0,0) = 2/pi.

Hence, for every real x including the removable origin,

  W_ext(x) = (pi/2) * Re rhoGamma(0,x).

This is an exact normalization bridge; no Fourier-transform or convolution
theorem is assumed.
-/

namespace GppWienerHopfGammaBridge

open GppMehlerFockSpectral
open GppWienerHopfWeightExtension
open GppSpectralRho
open GppSpectralRhoMehlerFock

/-- **Global Wiener--Hopf/Gamma bridge**, including the removable origin. -/
theorem extendedWienerHopfWeight_eq_pi_half_rhoGamma_zero_re (x : ℝ) :
    extendedWienerHopfWeight x =
      (Real.pi / 2) * (rhoGamma 0 x).re := by
  by_cases hx : x = 0
  · subst x
    rw [extendedWienerHopfWeight_zero, rhoGamma_zero_zero]
    simp
    field_simp [Real.pi_ne_zero]
  · have hrho :
        (rhoGamma 0 x).re = 2 * x / Real.sinh (Real.pi * x) := by
      rw [rhoGamma_zero_eq_mehlerFock x hx]
      rfl
    rw [extendedWienerHopfWeight_eq hx, hrho]
    unfold wienerHopfWeight
    have hsinh : Real.sinh (Real.pi * x) ≠ 0 := by
      exact Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hx)
    field_simp [hsinh]
    ring

/-- The same bridge solved for the real Gamma density. -/
theorem rhoGamma_zero_re_eq_two_over_pi_mul_extendedWienerHopfWeight (x : ℝ) :
    (rhoGamma 0 x).re =
      (2 / Real.pi) * extendedWienerHopfWeight x := by
  have h := extendedWienerHopfWeight_eq_pi_half_rhoGamma_zero_re x
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi] at h ⊢
  linarith

end GppWienerHopfGammaBridge

#print axioms GppWienerHopfGammaBridge.extendedWienerHopfWeight_eq_pi_half_rhoGamma_zero_re
#print axioms GppWienerHopfGammaBridge.rhoGamma_zero_re_eq_two_over_pi_mul_extendedWienerHopfWeight
