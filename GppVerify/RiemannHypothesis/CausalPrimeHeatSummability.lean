import GppVerify.RiemannHypothesis.CausalPrimeHeatBridge
import GppVerify.RiemannHypothesis.VonMangoldtCumulantSummability
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
# Absolute summability of the causal prime heat series

For fixed heat time `t > 0`, the normalized von-Mangoldt heat summand is

  (Lambda(n) / sqrt(n)) * (4*pi*t)^(-1/2) * exp(-(log n)^2/(4t)).

The Gaussian in `log n` eventually beats every fixed Dirichlet power.  We use only the
concrete comparison needed here: once `log n >= 8t`,

  exp(-(log n)^2/(4t)) <= n^(-2).

Since `1/sqrt(n) <= 1` for `n >= 1`, the unnormalized heat term is eventually bounded by
`Lambda(n)/n^2`.  The latter is absolutely summable because the von-Mangoldt L-series is
absolutely convergent at `s=2`.  A constant normalization then gives absolute summability
of the causal heat series.
-/

namespace GppCausalPrimeHeatSummability

open Filter
open ArithmeticFunction
open GppGlobalVonMangoldt
open GppCausalHeatBoundaryAnomaly
open GppCausalPrimeHeatBridge
open scoped LSeries.notation ArithmeticFunction

/-- Real Dirichlet majorant used for the heat comparison. -/
noncomputable def vonMangoldtDivSq (n : ℕ) : ℝ :=
  if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2

/-- The real majorant `Lambda(n)/n^2` is summable. -/
theorem summable_vonMangoldtDivSq : Summable vonMangoldtDivSq := by
  have hL : LSeriesSummable vonMangoldtComplex (2 : ℂ) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term vonMangoldtComplex (2 : ℂ) n‖) :=
    (summable_norm_iff).2 hL
  have heq : (fun n : ℕ => ‖LSeries.term vonMangoldtComplex (2 : ℂ) n‖) =
      vonMangoldtDivSq := by
    funext n
    rw [LSeries.norm_term_eq]
    unfold vonMangoldtDivSq vonMangoldtComplex
    split_ifs with hn
    · rfl
    · have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n :=
        ArithmeticFunction.vonMangoldt_nonneg
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
      norm_num
  rw [heq] at hnorm
  exact hnorm

/-- Unnormalized von-Mangoldt heat summand. -/
noncomputable def primeHeatCore (t : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
    Real.exp (-(Real.log n) ^ 2 / (4 * t))

/-- Beyond the explicit logarithmic threshold, the heat Gaussian is bounded by `n^-2`. -/
theorem heatGaussian_le_inv_sq_eventually {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-(Real.log n) ^ 2 / (4 * t)) ≤ 1 / (n : ℝ) ^ 2 := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (Real.exp (8 * t))
  filter_upwards [eventually_ge_atTop (max N 2)] with n hn
  have hnN : N ≤ n := le_trans (le_max_left N 2) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right N 2) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hexple : Real.exp (8 * t) ≤ (n : ℝ) := by
    exact le_trans (le_of_lt hN) (by exact_mod_cast hnN)
  have hlog : 8 * t ≤ Real.log n :=
    (Real.le_log_iff_exp_le hnpos).2 hexple
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hquad : 2 * Real.log n ≤ (Real.log n) ^ 2 / (4 * t) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * t)]
    nlinarith [mul_nonneg hlog0 (sub_nonneg.mpr hlog)]
  have hgauss :
      Real.exp (-(Real.log n) ^ 2 / (4 * t)) ≤ Real.exp (-2 * Real.log n) := by
    exact Real.exp_le_exp.mpr (by
      simpa [neg_div] using (neg_le_neg hquad))
  have hexp_inv : Real.exp (-2 * Real.log n) = 1 / (n : ℝ) ^ 2 := by
    calc
      Real.exp (-2 * Real.log n) =
          Real.exp (-Real.log n) * Real.exp (-Real.log n) := by
            rw [show -2 * Real.log n = -Real.log n + -Real.log n by ring,
              Real.exp_add]
      _ = (Real.exp (Real.log n))⁻¹ * (Real.exp (Real.log n))⁻¹ := by
            rw [Real.exp_neg]
      _ = 1 / (n : ℝ) ^ 2 := by
            rw [Real.exp_log hnpos]
            ring
  rwa [hexp_inv] at hgauss

/-- The unnormalized heat summand is eventually dominated by the summable Dirichlet majorant. -/
theorem primeHeatCore_le_majorant_eventually {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, ‖primeHeatCore t n‖ ≤ vonMangoldtDivSq n := by
  filter_upwards [heatGaussian_le_inv_sq_eventually ht, eventually_ge_atTop 2] with n hgauss hn2
  have hn0 : n ≠ 0 := by omega
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := by
    simpa using (Real.one_le_sqrt.mpr hn1)
  have hsqrtpos : 0 < Real.sqrt n := by positivity
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hfactor : ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤
      ArithmeticFunction.vonMangoldt n := by
    rw [div_le_iff₀ hsqrtpos]
    nlinarith
  have hgauss0 : 0 ≤ Real.exp (-(Real.log n) ^ 2 / (4 * t)) := Real.exp_nonneg _
  have hstep1 : primeHeatCore t n ≤
      ArithmeticFunction.vonMangoldt n * Real.exp (-(Real.log n) ^ 2 / (4 * t)) := by
    unfold primeHeatCore
    exact mul_le_mul_of_nonneg_right hfactor hgauss0
  have hstep2 : ArithmeticFunction.vonMangoldt n * Real.exp (-(Real.log n) ^ 2 / (4 * t)) ≤
      ArithmeticFunction.vonMangoldt n * (1 / (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hgauss hΛ
  have hcore0 : 0 ≤ primeHeatCore t n := by
    unfold primeHeatCore
    positivity
  unfold vonMangoldtDivSq
  rw [if_neg hn0]
  rw [Real.norm_eq_abs, abs_of_nonneg hcore0]
  calc
    primeHeatCore t n ≤ ArithmeticFunction.vonMangoldt n *
        Real.exp (-(Real.log n) ^ 2 / (4 * t)) := hstep1
    _ ≤ ArithmeticFunction.vonMangoldt n * (1 / (n : ℝ) ^ 2) := hstep2
    _ = ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 := by ring

/-- The unnormalized prime heat series is absolutely summable for every `t > 0`. -/
theorem summable_primeHeatCore {t : ℝ} (ht : 0 < t) :
    Summable (primeHeatCore t) :=
  Summable.of_norm_bounded_eventually_nat (g := vonMangoldtDivSq)
    summable_vonMangoldtDivSq (primeHeatCore_le_majorant_eventually ht)

/-- The normalized causal/von-Mangoldt heat series is absolutely summable for every positive
heat time. -/
theorem summable_normalizedPrimeHeatSummand {t : ℝ} (ht : 0 < t) :
    Summable (normalizedPrimeHeatSummand t) := by
  have hcore := summable_primeHeatCore ht
  have hconst : normalizedPrimeHeatSummand t =
      fun n : ℕ => (Real.sqrt (4 * Real.pi * t))⁻¹ * primeHeatCore t n := by
    funext n
    unfold normalizedPrimeHeatSummand heatKernelGaussian primeHeatCore
    ring
  rw [hconst]
  exact Summable.mul_left _ hcore

end GppCausalPrimeHeatSummability

#print axioms GppCausalPrimeHeatSummability.summable_vonMangoldtDivSq
#print axioms GppCausalPrimeHeatSummability.heatGaussian_le_inv_sq_eventually
#print axioms GppCausalPrimeHeatSummability.summable_primeHeatCore
#print axioms GppCausalPrimeHeatSummability.summable_normalizedPrimeHeatSummand
