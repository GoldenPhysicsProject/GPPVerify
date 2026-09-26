import GppVerify.RiemannHypothesis.ZetaFisherStrictMonotonicity
import Mathlib.Tactic

/-!
# Arithmetic identification and strict monotonicity of the actual zeta Fisher metric

The preceding arithmetic theorem proves strict decrease of the positive von-Mangoldt
Fisher series.  This file identifies that series with the already-defined Gibbs
log-energy variance.  Thus the strict order statement lands on the actual Fisher
metric used by the information-geometry layer, rather than on a parallel auxiliary
function.
-/

namespace GppZetaFisherArithmeticBridge

open Complex LSeries Set
open GppGlobalVonMangoldt
open GppZetaGibbsFisher
open GppZetaThirdCumulantStrict
open GppVonMangoldtCumulantDerivativeBridge
open GppZetaFisherStrictMonotonicity

/-- The explicit first response is the negative zeta variance response on `Re s>1`. -/
theorem firstResponse_eq_neg_zetaVarianceResponse
    {β : ℝ} (hβ : 1 < β) :
    firstResponse (β : ℂ) = -zetaVarianceResponse β := by
  have hne : riemannZeta (β : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_right_half_plane (by simpa using hβ)
  unfold firstResponse zetaVarianceResponse
  simp [iteratedDeriv_succ', iteratedDeriv_one]
  field_simp [hne]
  ring

/-- On the real Gibbs axis, the zeta variance response is exactly the once-logarithm
weighted von-Mangoldt L-series. -/
theorem zetaVarianceResponse_eq_logMul_vonMangoldt
    {β : ℝ} (hβ : 1 < β) :
    zetaVarianceResponse β =
      LSeries (LSeries.logMul vonMangoldtComplex) (β : ℂ) := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  have hsset : (β : ℂ) ∈ zetaHalfPlane := hs
  have heq :=
    (negZetaLogDeriv_eqOn_vonMangoldtLSeries.iteratedDeriv_of_isOpen
      isOpen_zetaHalfPlane 1) hsset
  have hder : deriv negZetaLogDeriv (β : ℂ) =
      deriv (LSeries vonMangoldtComplex) (β : ℂ) := by
    simpa [iteratedDeriv_one] using heq
  rw [deriv_negZetaLogDeriv_eq_firstResponse hs] at hder
  have habs : LSeries.abscissaOfAbsConv vonMangoldtComplex < ((β : ℂ).re) :=
    lt_of_le_of_lt abscissa_vonMangoldtComplex_le_one hs
  rw [LSeries_deriv habs] at hder
  rw [firstResponse_eq_neg_zetaVarianceResponse hβ] at hder
  exact neg_inj.mp hder

/-- The actual Gibbs Fisher metric is the positive arithmetic Fisher series. -/
theorem logEnergyVariance_eq_fisher_tsum
    {β : ℝ} (hβ : 1 < β) :
    logEnergyVariance β = ∑' n : ℕ, fisherSummand β n := by
  calc
    logEnergyVariance β = (zetaVarianceResponse β).re := by
      rw [zetaVarianceResponse_eq_ofReal_logEnergyVariance hβ]
      simp
    _ = (LSeries (LSeries.logMul vonMangoldtComplex) (β : ℂ)).re := by
      rw [zetaVarianceResponse_eq_logMul_vonMangoldt hβ]
    _ = ∑' n : ℕ, fisherSummand β n :=
      logMul_vonMangoldt_re_eq_fisher_tsum hβ

/-- **Strict Fisher decrease for the actual zeta Gibbs variance.** -/
theorem logEnergyVariance_strictAnti
    {β γ : ℝ} (hβ : 1 < β) (hβγ : β < γ) :
    logEnergyVariance γ < logEnergyVariance β := by
  have hγ : 1 < γ := hβ.trans hβγ
  rw [logEnergyVariance_eq_fisher_tsum hγ,
    logEnergyVariance_eq_fisher_tsum hβ]
  exact fisher_tsum_strictAnti hβ hβγ

end GppZetaFisherArithmeticBridge

#print axioms GppZetaFisherArithmeticBridge.zetaVarianceResponse_eq_logMul_vonMangoldt
#print axioms GppZetaFisherArithmeticBridge.logEnergyVariance_eq_fisher_tsum
#print axioms GppZetaFisherArithmeticBridge.logEnergyVariance_strictAnti
