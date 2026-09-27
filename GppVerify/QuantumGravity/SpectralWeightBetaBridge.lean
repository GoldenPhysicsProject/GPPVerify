import GppVerify.QuantumGravity.GammaModulusIdentity
import GppVerify.QuantumGravity.StefanBoltzmannFamily
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic

/-!
# The spectral weight as a complex Beta integral

The raw repository definition `P lam = pi*lam/sinh(pi*lam)` has the field-division junk
value `P 0 = 0`, although its removable continuous extension has value `1` at the origin.
For Fourier analysis we therefore introduce that continuous extension explicitly.

The key identity is

  `Pcont lam = Beta(1+i lam, 1-i lam)`

for every real `lam`. Away from zero this follows by combining the already-formalized
Gamma-modulus identity with `Gamma(s)Gamma(t)=Gamma(s+t)Beta(s,t)`; at zero the Beta
integral evaluates directly to `Beta(1,1)=1`.
-/

namespace GppSpectralWeightBeta

open Complex
open GppGammaModulus
open GppStefanBoltzmann

/-- Removable continuous extension of the spectral weight at the origin. -/
noncomputable def Pcont (lam : ℝ) : ℝ := if lam = 0 then 1 else P lam

@[simp] theorem Pcont_zero : Pcont 0 = 1 := by
  simp [Pcont]

/-- Away from the removable point, `Pcont` is the original spectral weight. -/
theorem Pcont_eq_P {lam : ℝ} (hlam : lam ≠ 0) : Pcont lam = P lam := by
  simp [Pcont, hlam]

/-- The Gamma product at principal-series conjugate points is exactly the Beta integral. -/
theorem gamma_product_eq_betaIntegral (lam : ℝ) :
    Complex.Gamma (1 + (lam : ℂ) * I) *
      Complex.Gamma (1 - (lam : ℂ) * I) =
    Complex.betaIntegral (1 + (lam : ℂ) * I) (1 - (lam : ℂ) * I) := by
  have hs : 0 < (1 + (lam : ℂ) * I).re := by simp
  have ht : 0 < (1 - (lam : ℂ) * I).re := by simp
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral hs ht
  have hsum : (1 + (lam : ℂ) * I) + (1 - (lam : ℂ) * I) = (2 : ℂ) := by ring
  have hG2 : Complex.Gamma (2 : ℂ) = 1 := by
    rw [show (2 : ℂ) = ((1 : ℕ) : ℂ) + 1 by norm_num,
      Complex.Gamma_nat_eq_factorial]
    norm_num
  rw [hsum, hG2, one_mul] at h
  exact h

/-- For nonzero `lam`, the original real spectral weight is the Beta integral. -/
theorem P_eq_betaIntegral {lam : ℝ} (hlam : lam ≠ 0) :
    ((P lam : ℝ) : ℂ) =
      Complex.betaIntegral (1 + (lam : ℂ) * I) (1 - (lam : ℂ) * I) := by
  rw [← gamma_product_eq_betaIntegral lam]
  exact (gamma_one_add_mul_gamma_one_sub lam hlam).symm

/-- **Global Beta representation of the continuous spectral weight.** -/
theorem Pcont_eq_betaIntegral (lam : ℝ) :
    ((Pcont lam : ℝ) : ℂ) =
      Complex.betaIntegral (1 + (lam : ℂ) * I) (1 - (lam : ℂ) * I) := by
  by_cases hlam : lam = 0
  · subst lam
    rw [Pcont_zero]
    norm_num
    have h := Complex.betaIntegral_eval_one_right (u := (1 : ℂ)) (by norm_num)
    simpa using h.symm
  · rw [Pcont_eq_P hlam]
    exact P_eq_betaIntegral hlam

end GppSpectralWeightBeta

#print axioms GppSpectralWeightBeta.Pcont_eq_betaIntegral
