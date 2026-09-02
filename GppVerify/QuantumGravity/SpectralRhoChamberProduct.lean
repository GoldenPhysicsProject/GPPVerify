import GppVerify.QuantumGravity.SpectralRhoRecurrence
import Mathlib.Tactic

/-!
# All-order chamber product for the normalized spectral Gamma family

The one-step recurrence telescopes exactly. Relative to the base weight
`rhoGamma 0`, every higher chamber is obtained by multiplication by an explicit
positive even polynomial and a factorial normalization. This is algebraic
special-function structure only; no convolution theorem is assumed.
-/

namespace GppSpectralRhoChamber

open Complex
open GppSpectralRho
open scoped BigOperators

noncomputable def chamberCoeff (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) / (((2 * k + 1).factorial : ℕ) : ℝ)

noncomputable def chamberPoly (k : ℕ) (x : ℝ) : ℝ :=
  ∏ j in Finset.range k, (((j : ℝ) + 1) ^ 2 + x ^ 2)

@[simp] theorem chamberCoeff_zero : chamberCoeff 0 = 1 := by
  norm_num [chamberCoeff]

@[simp] theorem chamberPoly_zero (x : ℝ) : chamberPoly 0 x = 1 := by
  simp [chamberPoly]

theorem chamberPoly_succ (k : ℕ) (x : ℝ) :
    chamberPoly (k + 1) x =
      chamberPoly k x * ((((k : ℝ) + 1) ^ 2) + x ^ 2) := by
  simp [chamberPoly, Finset.prod_range_succ]

theorem chamberCoeff_succ (k : ℕ) :
    chamberCoeff (k + 1) =
      (2 / (((k : ℝ) + 1) * (2 * (k : ℝ) + 3))) * chamberCoeff k := by
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hk23 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
  have hk22 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
  have hfact : (((2 * k + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hfac : (2 * (k + 1) + 1).factorial =
      (2 * k + 3) * (2 * k + 2) * (2 * k + 1).factorial := by
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega]
    rw [Nat.factorial_succ, Nat.factorial_succ]
    ring
  have hpow : (2 : ℝ) ^ (2 * (k + 1)) =
      4 * (2 : ℝ) ^ (2 * k) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
    norm_num
    ring
  unfold chamberCoeff
  rw [hfac, hpow]
  push_cast
  field_simp [hk1, hk23, hk22, hfact]
  ring

theorem rhoGamma_eq_chamberProduct_factored (k : ℕ) (x : ℝ) :
    rhoGamma k x =
      ((chamberCoeff k : ℝ) : ℂ) *
        ((chamberPoly k x : ℝ) : ℂ) * rhoGamma 0 x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [rhoGamma_succ, ih, chamberPoly_succ, chamberCoeff_succ]
      push_cast
      ring

theorem rhoGamma_eq_chamberProduct (k : ℕ) (x : ℝ) :
    rhoGamma k x =
      ((((2 : ℝ) ^ (2 * k) /
          (((2 * k + 1).factorial : ℕ) : ℝ) : ℝ) : ℂ) *
        ((chamberPoly k x : ℝ) : ℂ) * rhoGamma 0 x) := by
  simpa [chamberCoeff] using rhoGamma_eq_chamberProduct_factored k x

theorem chamberPoly_pos (k : ℕ) (x : ℝ) : 0 < chamberPoly k x := by
  unfold chamberPoly
  apply Finset.prod_pos
  intro j hj
  positivity

theorem chamberPoly_nonneg (k : ℕ) (x : ℝ) : 0 ≤ chamberPoly k x :=
  (chamberPoly_pos k x).le

end GppSpectralRhoChamber

#print axioms GppSpectralRhoChamber.chamberCoeff_succ
#print axioms GppSpectralRhoChamber.rhoGamma_eq_chamberProduct_factored
#print axioms GppSpectralRhoChamber.rhoGamma_eq_chamberProduct
#print axioms GppSpectralRhoChamber.chamberPoly_pos
