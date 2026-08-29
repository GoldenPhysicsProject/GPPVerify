import GppVerify.RiemannHypothesis.ZetaFisherStrictMonotonicity
import GppVerify.RiemannHypothesis.TwoParameterFisherDeterminant
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Strict monotonicity of the actual zeta-Gibbs Fisher metric

This file closes the interface between the positive arithmetic Fisher series and the
project's Gibbs variance.  Everything is restricted to the absolutely convergent
half-plane `β > 1`.
-/

namespace GppZetaGibbsFisherStrict

open Complex LSeries
open GppGlobalVonMangoldt
open GppZetaGibbsFisher
open GppZetaGibbsMoments
open GppZetaThirdCumulantStrict
open GppVonMangoldtCumulantDerivativeBridge
open GppVonMangoldtCumulantSummability
open GppZetaFisherStrictMonotonicity
open scoped LSeries.notation ArithmeticFunction Topology

/-- The derivative of the genuine negative logarithmic derivative is minus the
zeta variance response. -/
theorem deriv_negZetaLogDeriv_eq_neg_zetaVarianceResponse
    {β : ℝ} (hβ : 1 < β) :
    deriv negZetaLogDeriv (β : ℂ) = -zetaVarianceResponse β := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  rw [deriv_negZetaLogDeriv_eq_firstResponse hs]
  unfold firstResponse zetaVarianceResponse
  have hne : riemannZeta (β : ℂ) ≠ 0 := riemannZeta_ne_zero_right_half_plane hs
  simp [iteratedDeriv_succ', iteratedDeriv_one]
  field_simp [hne]
  ring

/-- The zeta variance response is exactly the once-logarithm-weighted von Mangoldt
L-series on the real Gibbs axis. -/
theorem zetaVarianceResponse_eq_logMul_vonMangoldt
    {β : ℝ} (hβ : 1 < β) :
    zetaVarianceResponse β =
      LSeries (LSeries.logMul vonMangoldtComplex) (β : ℂ) := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  have heq :
      deriv negZetaLogDeriv (β : ℂ) = deriv (LSeries vonMangoldtComplex) (β : ℂ) := by
    have hiter :=
      (negZetaLogDeriv_eqOn_vonMangoldtLSeries.iteratedDeriv_of_isOpen
        isOpen_zetaHalfPlane 1) hs
    simpa [iteratedDeriv_one] using hiter
  have hsE : (1 : EReal) < (((β : ℂ).re : ℝ) : EReal) := by
    exact_mod_cast hs
  have habs :
      LSeries.abscissaOfAbsConv vonMangoldtComplex < (((β : ℂ).re : ℝ) : EReal) :=
    lt_of_le_of_lt abscissa_vonMangoldtComplex_le_one hsE
  rw [deriv_negZetaLogDeriv_eq_neg_zetaVarianceResponse hβ] at heq
  rw [LSeries_deriv habs] at heq
  exact neg_injective heq

/-- The actual real Gibbs variance equals the positive arithmetic Fisher series. -/
theorem logEnergyVariance_eq_fisher_tsum
    {β : ℝ} (hβ : 1 < β) :
    logEnergyVariance β = ∑' n : ℕ, fisherSummand β n := by
  have hz := zetaVarianceResponse_eq_ofReal_logEnergyVariance hβ
  have hL := zetaVarianceResponse_eq_logMul_vonMangoldt hβ
  have hre :
      logEnergyVariance β =
        (LSeries (LSeries.logMul vonMangoldtComplex) (β : ℂ)).re := by
    rw [← hL, hz]
    simp
  rw [hre, logMul_vonMangoldt_re_eq_fisher_tsum hβ]

/-- **Strict Fisher monotonicity for the actual Gibbs variance**: if
`1 < β < γ`, then `g(γ) < g(β)`. -/
theorem logEnergyVariance_strictAnti
    {β γ : ℝ} (hβ : 1 < β) (hβγ : β < γ) :
    logEnergyVariance γ < logEnergyVariance β := by
  have hγ : 1 < γ := hβ.trans hβγ
  rw [logEnergyVariance_eq_fisher_tsum hγ]
  rw [logEnergyVariance_eq_fisher_tsum hβ]
  exact fisher_tsum_strictAnti hβ hβγ

end GppZetaGibbsFisherStrict

#print axioms GppZetaGibbsFisherStrict.zetaVarianceResponse_eq_logMul_vonMangoldt
#print axioms GppZetaGibbsFisherStrict.logEnergyVariance_eq_fisher_tsum
#print axioms GppZetaGibbsFisherStrict.logEnergyVariance_strictAnti
