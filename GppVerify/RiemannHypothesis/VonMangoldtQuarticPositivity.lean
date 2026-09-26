import GppVerify.RiemannHypothesis.VonMangoldtCumulantSummability
import GppVerify.RiemannHypothesis.VonMangoldtCosineBridge
import Mathlib.Tactic

/-!
# Strict positivity of the quartic von Mangoldt response

For real `β > 1`, the arithmetic series

  sum_n Λ(n) (log n)^3 exp(-β log n)

is absolutely summable and strictly positive.  This is the arithmetic sign layer
behind the fourth zeta-Gibbs cumulant response.  Identification with the genuine
fourth central cumulant is a separate analytic-algebraic bridge.
-/

namespace GppVonMangoldtQuarticPositivity

open Complex LSeries
open ArithmeticFunction
open GppGlobalVonMangoldt
open GppVonMangoldtCosine
open GppVonMangoldtCumulantSummability
open scoped LSeries.notation ArithmeticFunction

noncomputable def quarticSummand (β : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n *
    (Real.log n) ^ 3 * Real.exp (-Real.log n * β)

/-- The real part of the three-logarithm-weighted L-series term is exactly the
quartic arithmetic summand. -/
theorem logMul_three_term_re_eq_quarticSummand
    (n : ℕ) (β : ℝ) :
    (LSeries.term
      (LSeries.logMul (LSeries.logMul (LSeries.logMul vonMangoldtComplex)))
      (β : ℂ) n).re = quarticSummand β n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [quarticSummand, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn]
    rw [div_eq_mul_inv, ← Complex.cpow_neg]
    rw [Complex.mul_re]
    simp only [LSeries.logMul, vonMangoldtComplex]
    have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) :=
      Complex.natCast_log.symm
    rw [hlog]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, add_zero, sub_zero]
    have hpow0 := natCast_neg_cpow_re n hn β 0
    simp only [mul_zero, add_zero, Real.cos_zero, mul_one] at hpow0
    have hpow : (((n : ℂ) ^ (-(β : ℂ))).re) =
        Real.exp (-Real.log n * β) := by
      simpa using hpow0
    rw [hpow]
    unfold quarticSummand
    ring

/-- Absolute convergence of the real quartic von Mangoldt series for `β > 1`. -/
theorem summable_quarticSummand {β : ℝ} (hβ : 1 < β) :
    Summable (quarticSummand β) := by
  have hs := summable_iterated_logMul_vonMangoldt 3 hβ
  change Summable
    (fun n : ℕ =>
      LSeries.term
        ((LSeries.logMul^[3]) vonMangoldtComplex) (β : ℂ) n) at hs
  have hre : Summable
      (fun n : ℕ =>
        (LSeries.term
          ((LSeries.logMul^[3]) vonMangoldtComplex) (β : ℂ) n).re) :=
    Complex.reCLM.summable hs
  have hcoeff :
      ((LSeries.logMul^[3]) vonMangoldtComplex) =
        LSeries.logMul (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) := by
    simp [Function.iterate_succ_apply]
  rw [hcoeff] at hre
  exact hre.congr (fun n => logMul_three_term_re_eq_quarticSummand n β)

/-- Every quartic arithmetic term is nonnegative.  The only natural numbers
with potentially negative `log n` are `0` and `1`, where von Mangoldt vanishes;
for `n ≥ 2`, `log n ≥ 0`. -/
theorem quarticSummand_nonneg (β : ℝ) (n : ℕ) :
    0 ≤ quarticSummand β n := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> simp [quarticSummand]
  · have hn2 : 2 ≤ n := by omega
    have hlog : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    unfold quarticSummand
    exact mul_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (pow_nonneg hlog 3))
      (Real.exp_pos _).le

/-- The `n=2` term is strictly positive. -/
theorem quarticSummand_two_pos (β : ℝ) : 0 < quarticSummand β 2 := by
  unfold quarticSummand
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

/-- Strict positivity of the global quartic arithmetic response. -/
theorem tsum_quarticSummand_pos {β : ℝ} (hβ : 1 < β) :
    0 < ∑' n : ℕ, quarticSummand β n := by
  exact (summable_quarticSummand hβ).tsum_pos
    (quarticSummand_nonneg β) 2 (quarticSummand_two_pos β)

/-- The three-logarithm-weighted von Mangoldt L-series has strictly positive
real part on the real half-plane `β > 1`. -/
theorem logMul_three_vonMangoldt_re_pos {β : ℝ} (hβ : 1 < β) :
    0 < (LSeries
      (LSeries.logMul (LSeries.logMul (LSeries.logMul vonMangoldtComplex)))
      (β : ℂ)).re := by
  unfold LSeries
  have hs := summable_iterated_logMul_vonMangoldt 3 hβ
  change Summable
    (fun n : ℕ =>
      LSeries.term ((LSeries.logMul^[3]) vonMangoldtComplex) (β : ℂ) n) at hs
  have hcoeff :
      ((LSeries.logMul^[3]) vonMangoldtComplex) =
        LSeries.logMul (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) := by
    simp [Function.iterate_succ_apply]
  rw [hcoeff] at hs
  have hmap :
      (∑' n : ℕ,
        LSeries.term
          (LSeries.logMul (LSeries.logMul (LSeries.logMul vonMangoldtComplex)))
          (β : ℂ) n).re =
      ∑' n : ℕ,
        (LSeries.term
          (LSeries.logMul (LSeries.logMul (LSeries.logMul vonMangoldtComplex)))
          (β : ℂ) n).re := by
    simpa using (Complex.reCLM.map_tsum hs)
  rw [hmap]
  have heq :
      (∑' n : ℕ,
        (LSeries.term
          (LSeries.logMul (LSeries.logMul (LSeries.logMul vonMangoldtComplex)))
          (β : ℂ) n).re) =
        ∑' n : ℕ, quarticSummand β n := by
    apply tsum_congr
    intro n
    exact logMul_three_term_re_eq_quarticSummand n β
  rw [heq]
  exact tsum_quarticSummand_pos hβ

end GppVonMangoldtQuarticPositivity

#print axioms GppVonMangoldtQuarticPositivity.summable_quarticSummand
#print axioms GppVonMangoldtQuarticPositivity.tsum_quarticSummand_pos
#print axioms GppVonMangoldtQuarticPositivity.logMul_three_vonMangoldt_re_pos
