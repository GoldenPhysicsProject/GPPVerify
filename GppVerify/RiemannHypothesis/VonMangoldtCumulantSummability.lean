import GppVerify.RiemannHypothesis.GlobalVonMangoldtBridge
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Tactic

/-!
# Logarithm-weighted von Mangoldt summability

The strict zeta-Gibbs cumulant signs require more than termwise positivity: the
logarithm-weighted von Mangoldt series must first be known to converge absolutely.
Mathlib's L-series calculus supplies exactly this layer because `logMul` preserves
the abscissa of absolute convergence.

Everything here is restricted to the honest half-plane `β > 1`.
-/

namespace GppVonMangoldtCumulantSummability

open Complex LSeries
open ArithmeticFunction
open GppGlobalVonMangoldt
open scoped LSeries.notation ArithmeticFunction

/-- The von Mangoldt L-series has abscissa of absolute convergence at most `1`.
This is the only base convergence estimate needed below. -/
theorem abscissa_vonMangoldtComplex_le_one :
    LSeries.abscissaOfAbsConv vonMangoldtComplex ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt
    (show 1 < ((y : ℂ).re) by simpa using hy)

private theorem abscissa_vonMangoldtComplex_lt_beta
    {β : ℝ} (hβ : 1 < β) :
    LSeries.abscissaOfAbsConv vonMangoldtComplex < (((β : ℂ).re : ℝ) : EReal) := by
  have hβE : (1 : EReal) < (β : EReal) := by
    exact_mod_cast hβ
  exact lt_of_le_of_lt abscissa_vonMangoldtComplex_le_one (by simpa using hβE)

/-- One logarithmic insertion remains absolutely summable for every real `β > 1`. -/
theorem summable_logMul_vonMangoldt {β : ℝ} (hβ : 1 < β) :
    LSeriesSummable (LSeries.logMul vonMangoldtComplex) (β : ℂ) := by
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  simpa using abscissa_vonMangoldtComplex_lt_beta hβ

/-- Two logarithmic insertions remain absolutely summable for every real `β > 1`.
This is the convergence layer for the cubic zeta-Gibbs cumulant series
`Σ Λ(n) (log n)^2 n^{-β}`. -/
theorem summable_logMul_logMul_vonMangoldt {β : ℝ} (hβ : 1 < β) :
    LSeriesSummable
      (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) (β : ℂ) := by
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  simpa using abscissa_vonMangoldtComplex_lt_beta hβ

/-- In fact every finite number of logarithmic insertions has the same convergence
half-plane.  This is the analytic convergence spine for the full cumulant hierarchy. -/
theorem summable_iterated_logMul_vonMangoldt
    (m : ℕ) {β : ℝ} (hβ : 1 < β) :
    LSeriesSummable ((LSeries.logMul^[m]) vonMangoldtComplex) (β : ℂ) := by
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  simpa using abscissa_vonMangoldtComplex_lt_beta hβ

end GppVonMangoldtCumulantSummability

#print axioms GppVonMangoldtCumulantSummability.abscissa_vonMangoldtComplex_le_one
#print axioms GppVonMangoldtCumulantSummability.summable_logMul_logMul_vonMangoldt
#print axioms GppVonMangoldtCumulantSummability.summable_iterated_logMul_vonMangoldt
