import GppVerify.RiemannHypothesis.VonMangoldtPrimePowerReindex
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Absolute-convergence Fubini step for von-Mangoldt prime powers

On `a>1` the complex von-Mangoldt L-series is absolutely convergent. Hence its
real cosine summand is summable, the canonical `(prime,k)` reindexing is summable,
and the pair `tsum` may be split into an outer prime sum of inner prime-power sums.
-/

namespace GppVonMangoldtPrimePowerFubini

open Complex LSeries
open ArithmeticFunction
open GppGlobalVonMangoldt
open GppVonMangoldtCosine
open GppVonMangoldtPrimePowerReindex

/-- Absolute convergence of the real von-Mangoldt cosine summand for `a>1`. -/
theorem summable_cosineSummand {a : ℝ} (ha : 1 < a) (t : ℝ) :
    Summable (cosineSummand a t) := by
  have hs : 1 < (((a : ℂ) + (t : ℂ) * Complex.I).re) := by
    simpa using ha
  have hcomplex : Summable (fun n : ℕ =>
      LSeries.term vonMangoldtComplex
        ((a : ℂ) + (t : ℂ) * Complex.I) n) := by
    simpa [LSeriesSummable, vonMangoldtComplex] using
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
  have hreal : Summable (fun n : ℕ =>
      (LSeries.term vonMangoldtComplex
        ((a : ℂ) + (t : ℂ) * Complex.I) n).re) := by
    refine hcomplex.norm.of_norm_bounded ?_
    intro n
    simpa [Real.norm_eq_abs] using
      Complex.abs_re_le_norm
        (LSeries.term vonMangoldtComplex
          ((a : ℂ) + (t : ℂ) * Complex.I) n)
  refine hreal.congr ?_
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [cosineSummand]
  · exact (GppVonMangoldtCosine.vonMangoldt_term_re_eq_exp_cos n hn a t).symm

/-- The canonical prime-power pair summand is summable. -/
theorem summable_primePower_pair {a : ℝ} (ha : 1 < a) (t : ℝ) :
    Summable (fun pk : Nat.Primes × ℕ =>
      cosineSummand a t ((pk.1 : ℕ) ^ (pk.2 + 1))) := by
  let S : Set ℕ := {n : ℕ | IsPrimePow n}
  have hsub : Summable (fun n : S => cosineSummand a t n) :=
    (summable_cosineSummand ha t).subtype S
  have hpairs := (Nat.Primes.prodNatEquiv.summable_iff).2 hsub
  simpa [S] using hpairs

/-- Fubini/Tonelli rearrangement of the absolutely convergent prime-power pair sum. -/
theorem primePower_pair_tsum_eq_iterated {a : ℝ} (ha : 1 < a) (t : ℝ) :
    (∑' pk : Nat.Primes × ℕ,
      cosineSummand a t ((pk.1 : ℕ) ^ (pk.2 + 1))) =
      ∑' p : Nat.Primes, ∑' k : ℕ,
        cosineSummand a t ((p : ℕ) ^ (k + 1)) := by
  exact (summable_primePower_pair ha t).tsum_prod

/-- The global zeta response is therefore an outer prime sum of absolutely convergent
prime-power fibers. -/
theorem neg_zeta_logDeriv_re_eq_iterated_primePower_tsum
    {a t : ℝ} (ha : 1 < a) :
    (-(deriv riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I) /
      riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I))).re =
      ∑' p : Nat.Primes, ∑' k : ℕ,
        cosineSummand a t ((p : ℕ) ^ (k + 1)) := by
  rw [GppVonMangoldtPrimePowerReindex.neg_zeta_logDeriv_re_eq_primePower_pair_tsum ha]
  exact primePower_pair_tsum_eq_iterated ha t

end GppVonMangoldtPrimePowerFubini

#print axioms GppVonMangoldtPrimePowerFubini.summable_cosineSummand
#print axioms GppVonMangoldtPrimePowerFubini.primePower_pair_tsum_eq_iterated
#print axioms GppVonMangoldtPrimePowerFubini.neg_zeta_logDeriv_re_eq_iterated_primePower_tsum
