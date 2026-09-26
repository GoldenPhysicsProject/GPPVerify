import GppVerify.RiemannHypothesis.CausalHeatBoundaryAnomaly
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Finite causal prime-resolvent anomaly

The local causal prime resolvent is built from unilateral translations at repetition lengths

  a_m = (m+1) log p,

with Euler-log coefficients

  p^{-(m+1)/2} / (m+1).

The scalar boundary anomaly contributes an extra factor `a_m`. The repetition number
therefore cancels exactly, leaving the standard prime-orbit coefficient

  log p * p^{-(m+1)/2}.

For positive `p`, the remaining half-density factor is exactly the familiar prime-power
weight

  p^{-(m+1)/2} = 1 / sqrt(p^(m+1)).

Thus each finite causal repetition anomaly has precisely the arithmetic normalization used
by the von-Mangoldt heat term. This file does not construct the resolvent operator, prove
trace-class summability, or pass to the infinite prime/repetition sum.
-/

namespace GppCausalPrimeResolventFinite

open Finset
open GppCausalHeatBoundaryAnomaly

/-- Positive repetition number, indexed from zero to avoid a spurious `m=0` denominator. -/
def repetition (m : ℕ) : ℕ := m + 1

/-- Causal translation length of the `m`-th repetition of the prime orbit. -/
noncomputable def repetitionLength (p : ℝ) (m : ℕ) : ℝ :=
  (repetition m : ℝ) * Real.log p

/-- Euler-log resolvent coefficient attached to the `m`-th repetition. -/
noncomputable def resolventWeight (p : ℝ) (m : ℕ) : ℝ :=
  p ^ (-(repetition m : ℝ) / 2) / (repetition m : ℝ)

/-- The scalar heat-boundary anomaly at a translation length. -/
noncomputable def scalarHeatAnomaly (t a : ℝ) : ℝ :=
  a * heatKernelGaussian t a

/-- Square root commutes with every natural power of a nonnegative real number. -/
theorem sqrt_pow_nat {p : ℝ} (hp : 0 ≤ p) :
    ∀ n : ℕ, Real.sqrt (p ^ n) = Real.sqrt p ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hp n), sqrt_pow_nat hp n, pow_succ]

/-- The radial half-density weight is exactly inverse square-root normalization on the
corresponding prime power. -/
theorem rpow_neg_half_repetition_eq_inv_sqrt_pow
    {p : ℝ} (hp : 0 < p) (m : ℕ) :
    p ^ (-(repetition m : ℝ) / 2) =
      1 / Real.sqrt (p ^ repetition m) := by
  have hp0 : 0 ≤ p := hp.le
  have hneg : -(repetition m : ℝ) / 2 = -((repetition m : ℝ) / 2) := by ring
  rw [hneg, Real.rpow_neg hp0,
    Real.rpow_div_two_eq_sqrt (repetition m : ℝ) hp0,
    Real.rpow_natCast, one_div, sqrt_pow_nat hp0]

/-- **Euler repetition cancellation.** Multiplying the resolvent coefficient by the
boundary anomaly cancels the repetition denominator exactly. -/
theorem resolventWeight_mul_scalarHeatAnomaly
    (p t : ℝ) (m : ℕ) :
    resolventWeight p m * scalarHeatAnomaly t (repetitionLength p m) =
      Real.log p * p ^ (-(repetition m : ℝ) / 2) *
        heatKernelGaussian t (repetitionLength p m) := by
  have hmNat : repetition m ≠ 0 := by
    simp [repetition]
  have hm : (repetition m : ℝ) ≠ 0 := by
    exact_mod_cast hmNat
  unfold resolventWeight scalarHeatAnomaly repetitionLength
  field_simp [hm]
  ring

/-- The same repetition anomaly in literal von-Mangoldt prime-power normalization. -/
theorem resolventWeight_mul_scalarHeatAnomaly_eq_sqrt_weight
    {p : ℝ} (hp : 0 < p) (t : ℝ) (m : ℕ) :
    resolventWeight p m * scalarHeatAnomaly t (repetitionLength p m) =
      (Real.log p / Real.sqrt (p ^ repetition m)) *
        heatKernelGaussian t (repetitionLength p m) := by
  rw [resolventWeight_mul_scalarHeatAnomaly,
    rpow_neg_half_repetition_eq_inv_sqrt_pow hp]
  ring

/-- Closed Gaussian form of one weighted prime repetition anomaly. -/
theorem resolventWeight_mul_scalarHeatAnomaly_closed
    (p t : ℝ) (m : ℕ) :
    resolventWeight p m * scalarHeatAnomaly t (repetitionLength p m) =
      Real.log p * p ^ (-(repetition m : ℝ) / 2) *
        (Real.exp (-((repetition m : ℝ) * Real.log p) ^ 2 / (4 * t)) /
          Real.sqrt (4 * Real.pi * t)) := by
  rw [resolventWeight_mul_scalarHeatAnomaly]
  unfold heatKernelGaussian repetitionLength
  rfl

/-- Finite causal resolvent anomaly through repetition index `M-1`. -/
noncomputable def finiteResolventAnomaly (p t : ℝ) (M : ℕ) : ℝ :=
  ∑ m in range M,
    resolventWeight p m * scalarHeatAnomaly t (repetitionLength p m)

/-- Exact finite prime-orbit heat sum produced by the causal resolvent anomaly. -/
theorem finiteResolventAnomaly_eq_primeHeatSum
    (p t : ℝ) (M : ℕ) :
    finiteResolventAnomaly p t M =
      ∑ m in range M,
        Real.log p * p ^ (-(repetition m : ℝ) / 2) *
          heatKernelGaussian t (repetitionLength p m) := by
  unfold finiteResolventAnomaly
  apply Finset.sum_congr rfl
  intro m hm
  exact resolventWeight_mul_scalarHeatAnomaly p t m

/-- For positive `p`, the finite causal resolvent sum is already written with the literal
inverse-square-root prime-power coefficient. -/
theorem finiteResolventAnomaly_eq_sqrt_primeHeatSum
    {p : ℝ} (hp : 0 < p) (t : ℝ) (M : ℕ) :
    finiteResolventAnomaly p t M =
      ∑ m in range M,
        (Real.log p / Real.sqrt (p ^ repetition m)) *
          heatKernelGaussian t (repetitionLength p m) := by
  unfold finiteResolventAnomaly
  apply Finset.sum_congr rfl
  intro m hm
  exact resolventWeight_mul_scalarHeatAnomaly_eq_sqrt_weight hp t m

end GppCausalPrimeResolventFinite

#print axioms GppCausalPrimeResolventFinite.sqrt_pow_nat
#print axioms GppCausalPrimeResolventFinite.rpow_neg_half_repetition_eq_inv_sqrt_pow
#print axioms GppCausalPrimeResolventFinite.resolventWeight_mul_scalarHeatAnomaly
#print axioms GppCausalPrimeResolventFinite.resolventWeight_mul_scalarHeatAnomaly_eq_sqrt_weight
#print axioms GppCausalPrimeResolventFinite.finiteResolventAnomaly_eq_primeHeatSum
#print axioms GppCausalPrimeResolventFinite.finiteResolventAnomaly_eq_sqrt_primeHeatSum
