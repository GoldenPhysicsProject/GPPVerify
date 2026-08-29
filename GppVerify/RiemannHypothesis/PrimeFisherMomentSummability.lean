import GppVerify.RiemannHypothesis.PrimeHankelFisherSpecialization
import GppVerify.RiemannHypothesis.VonMangoldtCumulantSummability
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# All logarithmic Fisher moments are summable

For `β > 1`, the repaired all-order `logMul` convergence theorem implies absolute
summability of every arithmetic Fisher log-moment

  Λ(n) log(n) exp(-β log n) (log n)^r.

This is the monomial analytic input needed before finite polynomial-square packaging in
the all-order prime-gas Hankel theorem.
-/

namespace GppPrimeFisherMomentSummability

open Complex LSeries ArithmeticFunction
open GppGlobalVonMangoldt
open GppVonMangoldtCumulantSummability
open GppPrimeHankelFisherSpecialization
open scoped LSeries.notation ArithmeticFunction

/-- Iterating `logMul` multiplies an arbitrary coefficient sequence by the
corresponding power of the complex logarithm. -/
theorem iterated_logMul_apply_general (m n : ℕ) (f : ℕ → ℂ) :
    ((LSeries.logMul^[m]) f) n =
      (Complex.log n) ^ m * f n := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
      simp [Function.iterate_succ', Function.comp_def, ih, pow_succ,
        mul_assoc, mul_left_comm, mul_comm]

/-- Specialization of the generic coefficient identity to the von Mangoldt sequence. -/
theorem iterated_logMul_apply (m n : ℕ) :
    ((LSeries.logMul^[m]) vonMangoldtComplex) n =
      (Complex.log n) ^ m * vonMangoldtComplex n := by
  exact iterated_logMul_apply_general m n vonMangoldtComplex

/-- For a positive natural base, the real-axis complex power is exactly the embedded
Fisher exponential.  This uses `Complex.ofReal_cpow` and `Real.rpow_def_of_pos`, avoiding
branch-sensitive complex-log simplification. -/
theorem natCast_neg_cpow_eq_ofReal_exp
    (n : ℕ) (hn : n ≠ 0) (β : ℝ) :
    ((n : ℂ) ^ (-(β : ℂ))) =
      (Real.exp (-Real.log n * β) : ℂ) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  calc
    ((n : ℂ) ^ (-(β : ℂ))) = (((n : ℝ) ^ (-β) : ℝ) : ℂ) := by
      simpa using (Complex.ofReal_cpow hnpos.le (-β)).symm
    _ = (Real.exp (-Real.log n * β) : ℂ) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring

/-- The complete complex `(r+1)`-fold logarithm-weighted von Mangoldt L-series term
is the embedding of the corresponding real Fisher log-moment summand. -/
theorem iterated_logMul_term_eq_ofReal_fisher_moment
    (r n : ℕ) (β : ℝ) :
    LSeries.term ((LSeries.logMul^[r + 1]) vonMangoldtComplex) (β : ℂ) n =
      ((fisherWeight β n * (Real.log n) ^ r : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [fisherWeight, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, iterated_logMul_apply]
    rw [div_eq_mul_inv, ← Complex.cpow_neg]
    rw [natCast_neg_cpow_eq_ofReal_exp n hn β]
    have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) :=
      Complex.natCast_log.symm
    rw [hlog]
    simp only [vonMangoldtComplex]
    norm_cast
    unfold fisherWeight
    rw [pow_succ]
    ring

/-- The real part of the `(r+1)`-fold logarithm-weighted von Mangoldt L-series term
is exactly the `r`th Fisher log-moment summand. -/
theorem iterated_logMul_term_re_eq_fisher_moment
    (r n : ℕ) (β : ℝ) :
    (LSeries.term ((LSeries.logMul^[r + 1]) vonMangoldtComplex) (β : ℂ) n).re =
      fisherWeight β n * (Real.log n) ^ r := by
  have h := congrArg Complex.re
    (iterated_logMul_term_eq_ofReal_fisher_moment r n β)
  simpa only [Complex.ofReal_re] using h

/-- Every finite logarithmic moment of the actual prime-gas Fisher weight is summable
on the honest half-plane `β > 1`. -/
theorem summable_fisherWeight_mul_log_pow
    (r : ℕ) {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ => fisherWeight β n * (Real.log n) ^ r) := by
  have hs := summable_iterated_logMul_vonMangoldt (r + 1) hβ
  change Summable
    (fun n : ℕ =>
      LSeries.term ((LSeries.logMul^[r + 1]) vonMangoldtComplex) (β : ℂ) n) at hs
  have hre : Summable
      (fun n : ℕ =>
        (LSeries.term ((LSeries.logMul^[r + 1]) vonMangoldtComplex)
          (β : ℂ) n).re) :=
    Complex.reCLM.summable hs
  exact hre.congr (fun n => iterated_logMul_term_re_eq_fisher_moment r n β)

end GppPrimeFisherMomentSummability

#print axioms GppPrimeFisherMomentSummability.iterated_logMul_apply_general
#print axioms GppPrimeFisherMomentSummability.iterated_logMul_apply
#print axioms GppPrimeFisherMomentSummability.natCast_neg_cpow_eq_ofReal_exp
#print axioms GppPrimeFisherMomentSummability.iterated_logMul_term_eq_ofReal_fisher_moment
#print axioms GppPrimeFisherMomentSummability.summable_fisherWeight_mul_log_pow
