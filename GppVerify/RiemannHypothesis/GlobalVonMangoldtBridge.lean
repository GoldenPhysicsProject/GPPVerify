import Mathlib.NumberTheory.LSeries.Dirichlet
import GppVerify.RiemannHypothesis.CompletedLogDerivativeBridge
import Mathlib.Tactic

/-!
# Global von Mangoldt bridge

On the half-plane of absolute convergence, Mathlib proves that the L-series of the
von Mangoldt function is the genuine negative logarithmic derivative of the Riemann
zeta function.
-/

namespace GppGlobalVonMangoldt

open Complex LSeries Nat
open ArithmeticFunction
open scoped LSeries.notation ArithmeticFunction

/-- The complex-valued sequence obtained from the real von Mangoldt arithmetic function. -/
noncomputable def vonMangoldtComplex (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ)

/-- **Global prime-power logarithmic derivative in the absolute-convergence half-plane.** -/
theorem vonMangoldtLSeries_eq_neg_zeta_logDeriv {s : ℂ} (hs : 1 < s.re) :
    L vonMangoldtComplex s = - deriv riemannZeta s / riemannZeta s := by
  simpa [vonMangoldtComplex] using
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs)

/-- The Riemann zeta denominator occurring above is nonzero on `Re s > 1`. -/
theorem riemannZeta_ne_zero_right_half_plane {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ≠ 0 := by
  exact riemannZeta_ne_zero_of_one_lt_re hs

/-- Equivalent sign convention. -/
theorem neg_zeta_logDeriv_eq_vonMangoldtLSeries {s : ℂ} (hs : 1 < s.re) :
    -(deriv riemannZeta s / riemannZeta s) = L vonMangoldtComplex s := by
  have h := vonMangoldtLSeries_eq_neg_zeta_logDeriv hs
  rw [neg_div] at h
  exact h.symm

/-- The global logarithmic derivative is the explicit countable `tsum` of
von-Mangoldt L-series terms on `Re s > 1`. This is the stable infinite-series
object used for later real-part extraction and prime-power regrouping. -/
theorem neg_zeta_logDeriv_eq_tsum_vonMangoldt_terms {s : ℂ} (hs : 1 < s.re) :
    -(deriv riemannZeta s / riemannZeta s) =
      ∑' n : ℕ, LSeries.term vonMangoldtComplex s n := by
  rw [neg_zeta_logDeriv_eq_vonMangoldtLSeries hs]
  rfl

/-- The same response written as the literal Dirichlet `tsum`
`∑' n, Λ(n) / n^s`. This exact theorem survived on an older infinite-prime
research branch and is restored here because it is the most transparent discrete
arithmetic coordinate for the prime-power/Poisson transform program. -/
theorem neg_zeta_logDeriv_eq_tsum_vonMangoldt_div {s : ℂ} (hs : 1 < s.re) :
    -(deriv riemannZeta s / riemannZeta s) =
      ∑' n : ℕ, vonMangoldtComplex n / (n : ℂ) ^ s := by
  rw [neg_zeta_logDeriv_eq_vonMangoldtLSeries hs]
  have hs0 : s ≠ 0 := by
    intro h0
    subst s
    norm_num at hs
  unfold LSeries
  apply tsum_congr
  intro n
  exact LSeries.term_of_ne_zero' hs0 vonMangoldtComplex n

/-- Absolute convergence allows the real part to pass through the global
von-Mangoldt `tsum` on `Re s > 1`. This is the rigorous interchange step
needed before simplifying each term to the cosine kernel on `s = a + it`. -/
theorem neg_zeta_logDeriv_re_eq_tsum_re_terms {s : ℂ} (hs : 1 < s.re) :
    (-(deriv riemannZeta s / riemannZeta s)).re =
      ∑' n : ℕ, (LSeries.term vonMangoldtComplex s n).re := by
  rw [neg_zeta_logDeriv_eq_tsum_vonMangoldt_terms hs]
  have hsum : Summable (fun n : ℕ ↦ LSeries.term vonMangoldtComplex s n) := by
    simpa [LSeriesSummable, vonMangoldtComplex] using
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
  exact Complex.reCLM.map_tsum hsum

end GppGlobalVonMangoldt

#print axioms GppGlobalVonMangoldt.vonMangoldtLSeries_eq_neg_zeta_logDeriv
#print axioms GppGlobalVonMangoldt.riemannZeta_ne_zero_right_half_plane
#print axioms GppGlobalVonMangoldt.neg_zeta_logDeriv_eq_vonMangoldtLSeries
#print axioms GppGlobalVonMangoldt.neg_zeta_logDeriv_eq_tsum_vonMangoldt_terms
#print axioms GppGlobalVonMangoldt.neg_zeta_logDeriv_eq_tsum_vonMangoldt_div
#print axioms GppGlobalVonMangoldt.neg_zeta_logDeriv_re_eq_tsum_re_terms
