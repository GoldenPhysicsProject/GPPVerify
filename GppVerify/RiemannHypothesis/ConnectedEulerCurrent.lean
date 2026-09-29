import GppVerify.RiemannHypothesis.ZetaGibbsSummability
import Mathlib.Tactic

/-!
# Connected Euler-current summability thresholds

This module certifies the elementary analytic core behind the connected
half-density logarithmic Euler current.

The scalar Dirichlet logarithmic current uses an L1-type weight with exponent
1/2 + a and is summable by the existing zeta-Gibbs machinery once a > 1/2.
The Hilbert-square majorant uses exponent 1 + 2a and is summable for every
a > 0.

This is a domain theorem only. It does not prove RH and does not assert that
the scalar completed logarithmic derivative extends past its Euler domain.
-/

namespace GppConnectedEulerCurrent

open GppZetaGibbsSummability

/--
The square-majorant for a half-density logarithmic current is summable for
every positive displacement a.

Analytically this is
sum (log(n+1))^2 / (n+1)^(1+2a) < infinity,
the L2 threshold corresponding to Re(s - 1/2) = a > 0.
-/
theorem summable_log_sq_halfDensity
    {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ =>
      (Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 /
        (((n + 1 : ℕ) : ℝ) ^ (1 + 2 * a))) := by
  have hβ : (1 : ℝ) < 1 + 2 * a := by linarith
  have h :=
    GppZetaGibbsSummability.summable_gibbsWeight_mul_logEnergy_sq hβ
  exact h.congr (fun n => by
    simp [GppZetaGibbsSummability.gibbsWeight,
      GppZetaGibbsSummability.logEnergy, div_eq_mul_inv, mul_comm])

/--
The corresponding scalar logarithmic majorant is summable in the ordinary
Euler domain a > 1/2.

Analytically this is
sum log(n+1) / (n+1)^(1/2+a) < infinity.
-/
theorem summable_log_halfDensity_scalar
    {a : ℝ} (ha : (1 : ℝ) / 2 < a) :
    Summable (fun n : ℕ =>
      Real.log ((n + 1 : ℕ) : ℝ) /
        (((n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + a))) := by
  have hβ : (1 : ℝ) < (1 : ℝ) / 2 + a := by linarith
  have h :=
    GppZetaGibbsSummability.summable_gibbsWeight_mul_logEnergy hβ
  exact h.congr (fun n => by
    simp [GppZetaGibbsSummability.gibbsWeight,
      GppZetaGibbsSummability.logEnergy, div_eq_mul_inv, mul_comm])


/--
Finite logarithmic-current budget.

For every positive cutoff N, the harmonic-weighted logarithmic second moment
on 1,...,N is bounded by (log N)^2 times the harmonic mass:
sum_{n=1}^N (log n)^2/n <= (log N)^2 sum_{n=1}^N 1/n.

After normalizing by the harmonic mass, this is exactly the elementary
||j_N|| <= log N estimate for the finite zeta-graph current once the gauge
identity has converted the von Mangoldt current to log n / sqrt n.
No prime-distribution input is used.
-/
theorem finite_log_sq_harmonic_budget
    {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
        (Real.log (n : ℝ)) ^ 2 / (n : ℝ))
      ≤
    (Real.log (N : ℝ)) ^ 2 *
      (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) := by
  have hterm :
      ∀ n ∈ Finset.Icc 1 N,
        (Real.log (n : ℝ)) ^ 2 / (n : ℝ)
          ≤ (Real.log (N : ℝ)) ^ 2 * ((1 : ℝ) / (n : ℝ)) := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnN⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have hN_pos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hn_mem : (n : ℝ) ∈ Set.Ioi (0 : ℝ) := hn_pos
    have hN_mem : (N : ℝ) ∈ Set.Ioi (0 : ℝ) := hN_pos
    have hnN_real : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
    have hlog_le : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hn_mem hN_mem hnN_real
    have hlog_n_nonneg : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn1)
    have hlog_N_nonneg : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    have hsq :
        (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (N : ℝ)) ^ 2 := by
      nlinarith
    calc
      (Real.log (n : ℝ)) ^ 2 / (n : ℝ)
          ≤ (Real.log (N : ℝ)) ^ 2 / (n : ℝ) :=
            div_le_div_of_nonneg_right hsq hn_pos.le
      _ = (Real.log (N : ℝ)) ^ 2 * ((1 : ℝ) / (n : ℝ)) := by ring
  calc
    (∑ n ∈ Finset.Icc 1 N,
        (Real.log (n : ℝ)) ^ 2 / (n : ℝ))
      ≤ ∑ n ∈ Finset.Icc 1 N,
          (Real.log (N : ℝ)) ^ 2 * ((1 : ℝ) / (n : ℝ)) := by
            exact Finset.sum_le_sum fun n hn => hterm n hn
    _ = (Real.log (N : ℝ)) ^ 2 *
        (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) := by
          rw [Finset.mul_sum]

end GppConnectedEulerCurrent

#print axioms GppConnectedEulerCurrent.summable_log_sq_halfDensity
#print axioms GppConnectedEulerCurrent.summable_log_halfDensity_scalar
#print axioms GppConnectedEulerCurrent.finite_log_sq_harmonic_budget
