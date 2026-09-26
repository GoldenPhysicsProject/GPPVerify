import GppVerify.QuantumGravity.SpectralGammaPairRecurrence
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace GppSpectralRho

open Complex
open GppSpectralGammaPair

noncomputable def rhoGamma (k : ℕ) (x : ℝ) : ℂ :=
  (((2 : ℝ) ^ (2 * k + 1) /
      (Real.pi * ((2 * k + 1).factorial : ℝ)) : ℝ) : ℂ) *
    gammaPair ((k : ℝ) + 1) x

theorem rhoGamma_neg (k : ℕ) (x : ℝ) :
    rhoGamma k (-x) = rhoGamma k x := by
  unfold rhoGamma
  rw [gammaPair_neg]

/-- Exact one-step recurrence, proved by separating the real normalization ratio
from the Gamma recurrence before entering complex arithmetic. -/
theorem rhoGamma_succ (k : ℕ) (x : ℝ) :
    rhoGamma (k + 1) x =
      (((2 * ((((k : ℝ) + 1) ^ 2) + x ^ 2)) /
          (((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) : ℝ) : ℂ) *
        rhoGamma k x := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hk23 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
  have hk22 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
  have hfact : (((2 * k + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hgamma := gammaPair_add_one (a := (k : ℝ) + 1) (by positivity) x
  have hfac : (2 * (k + 1) + 1).factorial =
      (2 * k + 3) * (2 * k + 2) * (2 * k + 1).factorial := by
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega]
    rw [Nat.factorial_succ, Nat.factorial_succ]
    ring
  have hpow :
      (2 : ℝ) ^ (2 * (k + 1) + 1) =
        4 * (2 : ℝ) ^ (2 * k + 1) := by
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add]
    norm_num
    ring
  have hnorm :
      (2 : ℝ) ^ (2 * (k + 1) + 1) /
          (Real.pi * ((2 * (k + 1) + 1).factorial : ℝ)) =
        (2 / (((k : ℝ) + 1) * (2 * (k : ℝ) + 3))) *
          ((2 : ℝ) ^ (2 * k + 1) /
            (Real.pi * ((2 * k + 1).factorial : ℝ))) := by
    rw [hfac]
    push_cast
    rw [hpow]
    field_simp [hpi, hk1, hk23, hk22, hfact]
    ring
  unfold rhoGamma
  rw [show ((k + 1 : ℕ) : ℝ) + 1 = ((k : ℝ) + 1) + 1 by norm_num, hgamma]
  rw [hnorm]
  push_cast
  ring

noncomputable def rhoStepFactor (k : ℕ) (x : ℝ) : ℝ :=
  2 * ((((k : ℝ) + 1) ^ 2) + x ^ 2) /
    (((k : ℝ) + 1) * (2 * (k : ℝ) + 3))

/-- The Gamma-density recurrence packaged with the named real step factor. -/
theorem rhoGamma_succ_stepFactor (k : ℕ) (x : ℝ) :
    rhoGamma (k + 1) x = (rhoStepFactor k x : ℂ) * rhoGamma k x := by
  simpa [rhoStepFactor] using rhoGamma_succ k x

theorem rhoStepFactor_pos (k : ℕ) (x : ℝ) : 0 < rhoStepFactor k x := by
  unfold rhoStepFactor
  positivity

theorem rhoStepFactor_gt_one_iff (k : ℕ) (x : ℝ) :
    1 < rhoStepFactor k x ↔ ((k : ℝ) + 1) < 2 * x ^ 2 := by
  unfold rhoStepFactor
  have hden : 0 < ((k : ℝ) + 1) * (2 * (k : ℝ) + 3) := by positivity
  rw [lt_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith

theorem rhoStepFactor_lt_one_iff (k : ℕ) (x : ℝ) :
    rhoStepFactor k x < 1 ↔ 2 * x ^ 2 < ((k : ℝ) + 1) := by
  unfold rhoStepFactor
  have hden : 0 < ((k : ℝ) + 1) * (2 * (k : ℝ) + 3) := by positivity
  rw [div_lt_iff₀ hden]
  constructor <;> intro h <;> nlinarith

theorem rhoStepFactor_eq_one_iff (k : ℕ) (x : ℝ) :
    rhoStepFactor k x = 1 ↔ 2 * x ^ 2 = ((k : ℝ) + 1) := by
  unfold rhoStepFactor
  have hden : 0 < ((k : ℝ) + 1) * (2 * (k : ℝ) + 3) := by positivity
  rw [div_eq_iff hden.ne']
  constructor <;> intro h <;> nlinarith

theorem rhoStepFactor_zero_lt_one (k : ℕ) : rhoStepFactor k 0 < 1 := by
  rw [rhoStepFactor_lt_one_iff]
  norm_num
  positivity

end GppSpectralRho

#print axioms GppSpectralRho.rhoGamma_neg
#print axioms GppSpectralRho.rhoGamma_succ
#print axioms GppSpectralRho.rhoGamma_succ_stepFactor
#print axioms GppSpectralRho.rhoStepFactor_pos
#print axioms GppSpectralRho.rhoStepFactor_gt_one_iff
#print axioms GppSpectralRho.rhoStepFactor_lt_one_iff
#print axioms GppSpectralRho.rhoStepFactor_eq_one_iff
#print axioms GppSpectralRho.rhoStepFactor_zero_lt_one
