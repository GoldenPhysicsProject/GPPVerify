import GppVerify.RiemannHypothesis.VonMangoldtCumulantSummability
import GppVerify.RiemannHypothesis.VonMangoldtCosineBridge
import Mathlib.Tactic

/-!
# Strict positivity of the cubic von Mangoldt response

For real `β > 1`, the arithmetic series

  sum_n Λ(n) (log n)^2 exp(-β log n)

is absolutely summable and strictly positive.  The proof uses the L-series
summability layer for convergence, termwise nonnegativity of von Mangoldt, and the
explicit strictly positive `n=2` term.

This is the arithmetic sign input needed for the third zeta-Gibbs cumulant.  The
identification with the differentiated zeta response is a separate next layer.
-/

namespace GppVonMangoldtCubicPositivity

open Complex LSeries
open ArithmeticFunction
open GppGlobalVonMangoldt
open GppVonMangoldtCosine
open GppVonMangoldtCumulantSummability
open scoped LSeries.notation ArithmeticFunction

/-- Real cubic von Mangoldt summand. -/
noncomputable def cubicSummand (β : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n *
    (Real.log n) ^ 2 * Real.exp (-Real.log n * β)

/-- The real part of the twice-logarithm-weighted L-series term is exactly the
cubic arithmetic summand. -/
theorem logMul_logMul_term_re_eq_cubicSummand
    (n : ℕ) (β : ℝ) :
    (LSeries.term
      (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) (β : ℂ) n).re =
      cubicSummand β n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [cubicSummand, LSeries.term]
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
    unfold cubicSummand
    ring

/-- Absolute convergence of the real cubic von Mangoldt series for `β > 1`. -/
theorem summable_cubicSummand {β : ℝ} (hβ : 1 < β) :
    Summable (cubicSummand β) := by
  have hs := summable_logMul_logMul_vonMangoldt hβ
  change Summable
    (fun n : ℕ =>
      LSeries.term
        (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) (β : ℂ) n) at hs
  have hre : Summable
      (fun n : ℕ =>
        (LSeries.term
          (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) (β : ℂ) n).re) :=
    Complex.reCLM.summable hs
  exact hre.congr (fun n => logMul_logMul_term_re_eq_cubicSummand n β)

/-- Every cubic arithmetic term is nonnegative. -/
theorem cubicSummand_nonneg (β : ℝ) (n : ℕ) :
    0 ≤ cubicSummand β n := by
  unfold cubicSummand
  exact mul_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sq_nonneg _))
    (Real.exp_pos _).le

/-- The `n=2` term is strictly positive. -/
theorem cubicSummand_two_pos (β : ℝ) : 0 < cubicSummand β 2 := by
  unfold cubicSummand
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

/-- **Strict cubic positivity** in the honest Dirichlet-series half-plane. -/
theorem tsum_cubicSummand_pos {β : ℝ} (hβ : 1 < β) :
    0 < ∑' n : ℕ, cubicSummand β n := by
  exact (summable_cubicSummand hβ).tsum_pos
    (cubicSummand_nonneg β) 2 (cubicSummand_two_pos β)

/-- The twice-logarithm-weighted von Mangoldt L-series therefore has strictly
positive real part on the real half-plane `β > 1`. -/
theorem logMul_logMul_vonMangoldt_re_pos {β : ℝ} (hβ : 1 < β) :
    0 < (LSeries (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) (β : ℂ)).re := by
  unfold LSeries
  have hs := summable_logMul_logMul_vonMangoldt hβ
  change Summable
    (fun n : ℕ =>
      LSeries.term
        (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) (β : ℂ) n) at hs
  have hmap :
      (∑' n : ℕ,
        LSeries.term
          (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) (β : ℂ) n).re =
      ∑' n : ℕ,
        (LSeries.term
          (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) (β : ℂ) n).re := by
    simpa using (Complex.reCLM.map_tsum hs)
  rw [hmap]
  have heq :
      (∑' n : ℕ,
        (LSeries.term
          (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) (β : ℂ) n).re) =
        ∑' n : ℕ, cubicSummand β n := by
    apply tsum_congr
    intro n
    exact logMul_logMul_term_re_eq_cubicSummand n β
  rw [heq]
  exact tsum_cubicSummand_pos hβ

end GppVonMangoldtCubicPositivity

#print axioms GppVonMangoldtCubicPositivity.summable_cubicSummand
#print axioms GppVonMangoldtCubicPositivity.tsum_cubicSummand_pos
#print axioms GppVonMangoldtCubicPositivity.logMul_logMul_vonMangoldt_re_pos
