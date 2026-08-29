import GppVerify.RiemannHypothesis.ZetaThirdCumulantStrict
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# Strict monotonicity of the zeta-Gibbs Fisher metric

For `β > 1` the Fisher metric has the positive arithmetic expansion

  g(β) = sum_n Λ(n) log(n) exp(-β log n).

This file proves strict decrease directly at the series level.  It does not need to
pass through a real derivative theorem: if `1 < β < γ`, every arithmetic mode weakly
decreases and the `n=2` mode decreases strictly.
-/

namespace GppZetaFisherStrictMonotonicity

open Complex LSeries ArithmeticFunction
open GppGlobalVonMangoldt
open GppVonMangoldtCumulantSummability
open GppVonMangoldtCosine
open GppZetaGibbsFisher
open GppZetaThirdCumulantStrict
open GppVonMangoldtCumulantDerivativeBridge
open scoped LSeries.notation ArithmeticFunction

/-- Positive arithmetic Fisher summand. -/
noncomputable def fisherSummand (β : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Real.log n * Real.exp (-Real.log n * β)

/-- The real part of the once-logarithm-weighted von Mangoldt L-series term is the
arithmetic Fisher summand. -/
theorem logMul_term_re_eq_fisherSummand (n : ℕ) (β : ℝ) :
    (LSeries.term (LSeries.logMul vonMangoldtComplex) (β : ℂ) n).re =
      fisherSummand β n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [fisherSummand, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn]
    rw [div_eq_mul_inv, ← Complex.cpow_neg]
    rw [Complex.mul_re]
    simp only [LSeries.logMul, vonMangoldtComplex]
    have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := Complex.natCast_log.symm
    rw [hlog]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, add_zero, sub_zero]
    have hpow0 := natCast_neg_cpow_re n hn β 0
    simp only [mul_zero, add_zero, Real.cos_zero, mul_one] at hpow0
    have hpow : (((n : ℂ) ^ (-(β : ℂ))).re) =
        Real.exp (-Real.log n * β) := by
      simpa using hpow0
    rw [hpow]
    unfold fisherSummand
    ring

/-- Absolute convergence of the arithmetic Fisher series for `β>1`. -/
theorem summable_fisherSummand {β : ℝ} (hβ : 1 < β) :
    Summable (fisherSummand β) := by
  have hs := summable_logMul_vonMangoldt hβ
  change Summable
    (fun n : ℕ => LSeries.term (LSeries.logMul vonMangoldtComplex) (β : ℂ) n) at hs
  have hre : Summable
      (fun n : ℕ => (LSeries.term (LSeries.logMul vonMangoldtComplex) (β : ℂ) n).re) :=
    Complex.reCLM.summable hs
  exact hre.congr (fun n => logMul_term_re_eq_fisherSummand n β)

/-- Every arithmetic Fisher mode is nonnegative. -/
theorem fisherSummand_nonneg (β : ℝ) (n : ℕ) : 0 ≤ fisherSummand β n := by
  unfold fisherSummand
  have hlog : 0 ≤ Real.log n := by
    rcases n with _ | n
    · simp
    · exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  exact mul_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hlog)
    (Real.exp_pos _).le

/-- Raising inverse temperature weakly decreases each arithmetic Fisher mode. -/
theorem fisherSummand_antitone_pair
    {β γ : ℝ} (hβγ : β ≤ γ) (n : ℕ) :
    fisherSummand γ n ≤ fisherSummand β n := by
  unfold fisherSummand
  have hlog : 0 ≤ Real.log n := by
    rcases n with _ | n
    · simp
    · exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have hexp : Real.exp (-Real.log n * γ) ≤ Real.exp (-Real.log n * β) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul_of_nonneg_left hexp
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hlog)

/-- The `n=2` mode decreases strictly when `β<γ`. -/
theorem fisherSummand_two_strict
    {β γ : ℝ} (hβγ : β < γ) :
    fisherSummand γ 2 < fisherSummand β 2 := by
  unfold fisherSummand
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hexp : Real.exp (-Real.log 2 * γ) < Real.exp (-Real.log 2 * β) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  exact mul_lt_mul_of_pos_left hexp (mul_pos hlog hlog)

/-- **Strict arithmetic Fisher monotonicity**. -/
theorem fisher_tsum_strictAnti
    {β γ : ℝ} (hβ : 1 < β) (hβγ : β < γ) :
    (∑' n : ℕ, fisherSummand γ n) < ∑' n : ℕ, fisherSummand β n := by
  have hγ : 1 < γ := hβ.trans hβγ
  exact Summable.tsum_lt_tsum
    (fun n => fisherSummand_antitone_pair hβγ.le n)
    (fisherSummand_two_strict hβγ)
    (summable_fisherSummand hγ)
    (summable_fisherSummand hβ)

/-- The arithmetic Fisher sum is exactly the once-logarithm-weighted von Mangoldt
L-series on the real axis. -/
theorem logMul_vonMangoldt_re_eq_fisher_tsum
    {β : ℝ} (hβ : 1 < β) :
    (LSeries (LSeries.logMul vonMangoldtComplex) (β : ℂ)).re =
      ∑' n : ℕ, fisherSummand β n := by
  unfold LSeries
  have hs := summable_logMul_vonMangoldt hβ
  change Summable
    (fun n : ℕ => LSeries.term (LSeries.logMul vonMangoldtComplex) (β : ℂ) n) at hs
  change Complex.reCLM
      (∑' n : ℕ, LSeries.term (LSeries.logMul vonMangoldtComplex) (β : ℂ) n) =
    ∑' n : ℕ, fisherSummand β n
  rw [Complex.reCLM.map_tsum hs]
  apply tsum_congr
  intro n
  exact logMul_term_re_eq_fisherSummand n β

end GppZetaFisherStrictMonotonicity

#print axioms GppZetaFisherStrictMonotonicity.fisher_tsum_strictAnti
#print axioms GppZetaFisherStrictMonotonicity.logMul_vonMangoldt_re_eq_fisher_tsum
