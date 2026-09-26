import GppVerify.QuantumGravity.GammaModulusIdentity
import GppVerify.QuantumGravity.SpectralRhoChamberProduct
import Mathlib.Tactic

/-!
# Explicit Mehler--Fock bridge for the normalized Gamma spectral family

The normalized Gamma family `rhoGamma` and its all-order chamber product have already
been proved algebraically. Separately, Euler reflection gives the exact base Gamma
modulus

  Gamma(1+i x) Gamma(1-i x) = pi*x/sinh(pi*x)

for `x != 0`. This file joins those two kernel-proved facts.
-/

namespace GppSpectralRhoMehlerFock

open Complex
open GppSpectralRho
open GppSpectralRhoChamber

/-- The base normalized Gamma weight is the explicit Mehler--Fock density away from
its removable singularity at the origin. -/
theorem rhoGamma_zero_eq_mehlerFock (x : ℝ) (hx : x ≠ 0) :
    rhoGamma 0 x = ((2 * x / Real.sinh (Real.pi * x) : ℝ) : ℂ) := by
  have hgamma := GppGammaModulus.gamma_one_add_mul_gamma_one_sub x hx
  have hpiC : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hsinhC : Complex.sinh (((Real.pi : ℝ) : ℂ) * (x : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]
    exact_mod_cast Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hx)
  unfold rhoGamma GppSpectralGammaPair.gammaPair
  norm_num
  rw [hgamma]
  push_cast
  field_simp [hpiC, hsinhC]
  ring

/-- Exact value at the removable singularity of the base Mehler--Fock quotient. -/
theorem rhoGamma_zero_zero :
    rhoGamma 0 0 = ((2 / Real.pi : ℝ) : ℂ) := by
  unfold rhoGamma GppSpectralGammaPair.gammaPair
  norm_num

/-- At the origin the chamber polynomial is exactly `(k!)^2`. -/
theorem chamberPoly_at_zero (k : ℕ) :
    chamberPoly k 0 = (((k.factorial : ℝ)) ^ 2) := by
  induction k with
  | zero => simp [chamberPoly]
  | succ k ih =>
      rw [show k + 1 = Nat.succ k by rfl, chamberPoly_succ, ih]
      rw [Nat.factorial_succ]
      push_cast
      ring

/-- All-order removable-origin value of the normalized Gamma/Mehler--Fock chamber family. -/
theorem rhoGamma_at_zero (k : ℕ) :
    rhoGamma k 0 =
      (((2 : ℝ) ^ (2 * k + 1) * (k.factorial : ℝ) ^ 2 /
        (((2 * k + 1).factorial : ℝ) * Real.pi) : ℝ) : ℂ) := by
  rw [rhoGamma_eq_chamberProduct, rhoGamma_zero_zero, chamberPoly_at_zero]
  have hfact : ((2 * k + 1).factorial : ℝ) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpow : (2 : ℝ) ^ (2 * k + 1) = 2 * (2 : ℝ) ^ (2 * k) := by
    rw [pow_succ]
    ring
  rw [hpow]
  push_cast
  field_simp [hfact, hpi]
  ring

/-- All-order explicit Mehler--Fock chamber formula away from `x=0`. -/
theorem rhoGamma_eq_mehlerFock_chamber (k : ℕ) (x : ℝ) (hx : x ≠ 0) :
    rhoGamma k x =
      (((2 : ℝ) ^ (2 * k + 1) * x * chamberPoly k x /
        (((2 * k + 1).factorial : ℝ) * Real.sinh (Real.pi * x)) : ℝ) : ℂ) := by
  rw [rhoGamma_eq_chamberProduct, rhoGamma_zero_eq_mehlerFock x hx]
  have hfact : ((2 * k + 1).factorial : ℝ) ≠ 0 := by positivity
  have hsinh : Real.sinh (Real.pi * x) ≠ 0 := by
    exact Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hx)
  have hpow : (2 : ℝ) ^ (2 * k + 1) = 2 * (2 : ℝ) ^ (2 * k) := by
    rw [pow_succ]
    ring
  rw [hpow]
  push_cast
  field_simp [hfact, hsinh]
  ring

/-- Unified all-real chamber formula, with the removable origin value filled in. -/
theorem rhoGamma_eq_mehlerFock_chamber_all (k : ℕ) (x : ℝ) :
    rhoGamma k x =
      if x = 0 then
        (((2 : ℝ) ^ (2 * k + 1) * (k.factorial : ℝ) ^ 2 /
          (((2 * k + 1).factorial : ℝ) * Real.pi) : ℝ) : ℂ)
      else
        (((2 : ℝ) ^ (2 * k + 1) * x * chamberPoly k x /
          (((2 * k + 1).factorial : ℝ) * Real.sinh (Real.pi * x)) : ℝ) : ℂ) := by
  by_cases hx : x = 0
  · subst x
    simp only [if_pos rfl]
    exact rhoGamma_at_zero k
  · simp only [if_neg hx]
    exact rhoGamma_eq_mehlerFock_chamber k x hx

end GppSpectralRhoMehlerFock

#print axioms GppSpectralRhoMehlerFock.rhoGamma_zero_eq_mehlerFock
#print axioms GppSpectralRhoMehlerFock.rhoGamma_zero_zero
#print axioms GppSpectralRhoMehlerFock.chamberPoly_at_zero
#print axioms GppSpectralRhoMehlerFock.rhoGamma_at_zero
#print axioms GppSpectralRhoMehlerFock.rhoGamma_eq_mehlerFock_chamber
#print axioms GppSpectralRhoMehlerFock.rhoGamma_eq_mehlerFock_chamber_all
