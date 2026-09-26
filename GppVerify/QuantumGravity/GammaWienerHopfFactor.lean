import GppVerify.QuantumGravity.GammaHalfModulusIdentity
import Mathlib.Tactic

/-!
# Normalized Gamma Wiener--Hopf factor on the real spectral axis

Define the two normalized half-Gamma factors

  Hplus(k)  = Gamma(1/2 - i k/(2*pi))^2 / pi,
  Hminus(k) = Gamma(1/2 + i k/(2*pi))^2 / pi.

The previously formalized half-shift reflection identity implies exactly

  Hplus(k) Hminus(k) = sech(k/2)^2.

This file proves the real-axis factorization and its integer-power semigroup.  It does
not claim the half-plane holomorphy/outer-function part of Wiener--Hopf theory; that is a
separate complex-analysis layer.
-/

namespace GppGammaWienerHopf

open Complex
open scoped ComplexConjugate

/-- Upper-half-plane candidate factor, restricted here to real spectral parameter `k`. -/
noncomputable def Hplus (k : ℝ) : ℂ :=
  Complex.Gamma (((1 : ℂ) / 2) -
      (((k / (2 * Real.pi) : ℝ) : ℂ) * I)) ^ 2 / (Real.pi : ℂ)

/-- Lower-half-plane candidate factor, restricted here to real spectral parameter `k`. -/
noncomputable def Hminus (k : ℝ) : ℂ :=
  Complex.Gamma (((1 : ℂ) / 2) +
      (((k / (2 * Real.pi) : ℝ) : ℂ) * I)) ^ 2 / (Real.pi : ℂ)

/-- On the real spectral axis the two normalized Gamma factors are complex conjugates. -/
theorem Hminus_eq_conj_Hplus (k : ℝ) :
    Hminus k = conj (Hplus k) := by
  have hstar2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    change conj (2 : ℂ) = 2
    apply Complex.ext <;> norm_num
  have harg :
      conj (((1 : ℂ) / 2) - (((k / (2 * Real.pi) : ℝ) : ℂ) * I)) =
        ((1 : ℂ) / 2) + (((k / (2 * Real.pi) : ℝ) : ℂ) * I) := by
    simp [hstar2]
  have hgamma :
      Complex.Gamma (((1 : ℂ) / 2) +
          (((k / (2 * Real.pi) : ℝ) : ℂ) * I)) =
        conj (Complex.Gamma (((1 : ℂ) / 2) -
          (((k / (2 * Real.pi) : ℝ) : ℂ) * I))) := by
    rw [← Complex.Gamma_conj, harg]
  unfold Hminus Hplus
  rw [hgamma]
  simp [hstar2]

/-- Consequently the two real-axis factors have exactly the same modulus. -/
theorem norm_Hminus_eq_norm_Hplus (k : ℝ) :
    ‖Hminus k‖ = ‖Hplus k‖ := by
  rw [Hminus_eq_conj_Hplus]
  simp

/-- **Exact normalized Gamma factorization** of the `sech^2` spectral multiplier. -/
theorem Hplus_mul_Hminus (k : ℝ) :
    Hplus k * Hminus k =
      ((1 / (Real.cosh (k / 2)) ^ 2 : ℝ) : ℂ) := by
  have href := GppGammaHalfModulus.gamma_half_add_mul_gamma_half_sub
    (k / (2 * Real.pi))
  have hscale : Real.pi * (k / (2 * Real.pi)) = k / 2 := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [hscale] at href
  calc
    Hplus k * Hminus k =
        (Complex.Gamma (((1 : ℂ) / 2) +
            (((k / (2 * Real.pi) : ℝ) : ℂ) * I)) *
          Complex.Gamma (((1 : ℂ) / 2) -
            (((k / (2 * Real.pi) : ℝ) : ℂ) * I))) ^ 2 /
          (Real.pi : ℂ) ^ 2 := by
            unfold Hplus Hminus
            ring
    _ = ((((Real.pi / Real.cosh (k / 2) : ℝ) : ℂ) ^ 2) /
          (Real.pi : ℂ) ^ 2) := by rw [href]
    _ = ((1 / (Real.cosh (k / 2)) ^ 2 : ℝ) : ℂ) := by
      have hcosh : Real.cosh (k / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
      have hreal :
          (Real.pi / Real.cosh (k / 2)) ^ 2 / Real.pi ^ 2 =
            1 / Real.cosh (k / 2) ^ 2 := by
        field_simp [Real.pi_ne_zero, hcosh]
        ring
      exact_mod_cast hreal

/-- The upper real-axis Gamma factor never vanishes.  This follows directly from
its exact product with the lower factor and positivity of `cosh`. -/
theorem Hplus_ne_zero (k : ℝ) : Hplus k ≠ 0 := by
  intro hz
  have hfactor := Hplus_mul_Hminus k
  rw [hz, zero_mul] at hfactor
  have hcosh : Real.cosh (k / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hrhs : ((1 / (Real.cosh (k / 2)) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (div_ne_zero one_ne_zero (pow_ne_zero 2 hcosh))
  exact hrhs hfactor.symm

/-- The lower real-axis Gamma factor never vanishes. -/
theorem Hminus_ne_zero (k : ℝ) : Hminus k ≠ 0 := by
  rw [Hminus_eq_conj_Hplus]
  simpa using Hplus_ne_zero k

/-- The real-axis quotient is a pure phase: it has exactly unit modulus.
This is a real-axis statement only and does not assert a Hardy-space inner factor. -/
theorem norm_Hminus_div_Hplus (k : ℝ) :
    ‖Hminus k / Hplus k‖ = 1 := by
  rw [norm_div, norm_Hminus_eq_norm_Hplus, div_self]
  exact norm_ne_zero_iff.mpr (Hplus_ne_zero k)

/-- Every integer chamber power of the real-axis phase remains unimodular. -/
theorem norm_Hminus_div_Hplus_pow (m : ℕ) (k : ℝ) :
    ‖(Hminus k / Hplus k) ^ m‖ = 1 := by
  rw [norm_pow, norm_Hminus_div_Hplus, one_pow]

/-- Every integer chamber inherits the same factorization multiplicatively. -/
theorem Hplus_pow_mul_Hminus_pow (m : ℕ) (k : ℝ) :
    Hplus k ^ m * Hminus k ^ m =
      (((1 / (Real.cosh (k / 2)) ^ 2 : ℝ) : ℂ) ^ m) := by
  rw [← mul_pow, Hplus_mul_Hminus]

end GppGammaWienerHopf

#print axioms GppGammaWienerHopf.Hminus_eq_conj_Hplus
#print axioms GppGammaWienerHopf.norm_Hminus_eq_norm_Hplus
#print axioms GppGammaWienerHopf.Hplus_mul_Hminus
#print axioms GppGammaWienerHopf.Hplus_ne_zero
#print axioms GppGammaWienerHopf.Hminus_ne_zero
#print axioms GppGammaWienerHopf.norm_Hminus_div_Hplus
#print axioms GppGammaWienerHopf.norm_Hminus_div_Hplus_pow
#print axioms GppGammaWienerHopf.Hplus_pow_mul_Hminus_pow
