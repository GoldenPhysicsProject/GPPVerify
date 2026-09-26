import GppVerify.QuantumGravity.SpectralRhoMehlerFockBridge
import Mathlib.Tactic

/-!
# Positivity of the normalized Mehler--Fock chamber weights

The explicit all-order chamber formula makes positivity transparent.  Every
chamber polynomial is strictly positive, `x` and `sinh(pi*x)` have the same sign,
and the removable origin value is strictly positive.  Hence the normalized
Gamma/Mehler--Fock spectral density is a positive real number for every real
principal-series parameter.
-/

namespace GppSpectralRhoPositivity

open Complex
open GppSpectralRho
open GppSpectralRhoChamber
open GppSpectralRhoMehlerFock

/-- The chamber polynomial is strictly positive at every real spectral parameter. -/
theorem chamberPoly_pos (k : ℕ) (x : ℝ) :
    0 < chamberPoly k x := by
  unfold chamberPoly
  apply Finset.prod_pos
  intro j hj
  positivity

/-- Every normalized Gamma/Mehler--Fock chamber weight has zero imaginary part. -/
theorem rhoGamma_im_eq_zero (k : ℕ) (x : ℝ) :
    (rhoGamma k x).im = 0 := by
  by_cases hx : x = 0
  · subst x
    rw [rhoGamma_at_zero]
    simp
  · rw [rhoGamma_eq_mehlerFock_chamber k x hx]
    simp

/-- **Strict spectral positivity**: every normalized Gamma/Mehler--Fock chamber
weight lies on the positive real axis. -/
theorem rhoGamma_re_pos (k : ℕ) (x : ℝ) :
    0 < (rhoGamma k x).re := by
  by_cases hx0 : x = 0
  · subst x
    rw [rhoGamma_at_zero]
    simp only [ofReal_re]
    positivity
  · rw [rhoGamma_eq_mehlerFock_chamber k x hx0]
    simp only [ofReal_re]
    have hpoly : 0 < chamberPoly k x := chamberPoly_pos k x
    have hpow : 0 < (2 : ℝ) ^ (2 * k + 1) := by positivity
    have hfact : 0 < (((2 * k + 1).factorial : ℕ) : ℝ) := by positivity
    rcases lt_or_gt_of_ne hx0 with hx | hx
    · have hsinh : Real.sinh (Real.pi * x) < 0 :=
        Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg Real.pi_pos hx)
      have hnum :
          (2 : ℝ) ^ (2 * k + 1) * x * chamberPoly k x < 0 := by
        positivity
      have hden :
          (((2 * k + 1).factorial : ℕ) : ℝ) * Real.sinh (Real.pi * x) < 0 := by
        positivity
      exact div_pos_of_neg_of_neg hnum hden
    · have hsinh : 0 < Real.sinh (Real.pi * x) :=
        Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hx)
      positivity

end GppSpectralRhoPositivity

#print axioms GppSpectralRhoPositivity.chamberPoly_pos
#print axioms GppSpectralRhoPositivity.rhoGamma_im_eq_zero
#print axioms GppSpectralRhoPositivity.rhoGamma_re_pos
