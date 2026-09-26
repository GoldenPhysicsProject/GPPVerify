import GppVerify.RiemannHypothesis.ZetaGibbsThermodynamicDerivatives
import GppVerify.RiemannHypothesis.ZetaThirdCumulantStrict
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
# Differential cumulant hierarchy for the zeta Gibbs family

On the honest Gibbs half-line `beta > 1`, the variance is the real part of the
once-logarithm-weighted von Mangoldt L-series. Differentiating that absolutely
convergent L-series inserts one further logarithm and a minus sign. The existing
third-cumulant bridge identifies the resulting twice-logarithm-weighted series
with the genuine third central moment. Thus

  d/d beta Var_beta(log n) = - kappa_3(beta).

No analytic continuation of this thermodynamic identity is asserted.
-/

namespace GppZetaGibbsCumulantDerivative

open Complex LSeries Set Filter
open GppGlobalVonMangoldt
open GppVonMangoldtCumulantSummability
open GppVonMangoldtCumulantDerivativeBridge
open GppZetaGibbsFisher
open GppZetaGibbsFisherStrict
open GppZetaThirdCumulantStrict
open scoped LSeries.notation ArithmeticFunction Topology

/-- The genuine Gibbs variance is the real part of the once-log-weighted
von Mangoldt L-series. -/
theorem logEnergyVariance_eq_logMul_re
    {β : ℝ} (hβ : 1 < β) :
    logEnergyVariance β =
      (LSeries (LSeries.logMul vonMangoldtComplex) (β : ℂ)).re := by
  have hz := zetaVarianceResponse_eq_ofReal_logEnergyVariance hβ
  have hL := zetaVarianceResponse_eq_logMul_vonMangoldt hβ
  calc
    logEnergyVariance β = ((logEnergyVariance β : ℂ)).re := by simp
    _ = (zetaVarianceResponse β).re := by rw [hz]
    _ = (LSeries (LSeries.logMul vonMangoldtComplex) (β : ℂ)).re := by rw [hL]

/-- The twice-log-weighted von Mangoldt L-series is the real third Gibbs cumulant
on the honest Gibbs axis. -/
theorem logMul_logMul_vonMangoldt_re_eq_thirdCumulant
    {β : ℝ} (hβ : 1 < β) :
    (LSeries (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) (β : ℂ)).re =
      logEnergyThirdCumulant β := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  have hbridge := iteratedDeriv_two_negZetaLogDeriv_eq_logMul_logMul hs
  have hresp := iteratedDeriv_two_negZetaLogDeriv_eq_zetaThirdCumulantResponse hβ
  have hz := zetaThirdCumulantResponse_eq_ofReal_logEnergyThirdCumulant hβ
  have hcomplex :
      LSeries (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) (β : ℂ) =
        (logEnergyThirdCumulant β : ℂ) := by
    rw [← hbridge, hresp, hz]
  rw [hcomplex]
  simp

/-- **Exact second-to-third cumulant differential law**:
`d Var_beta(log n) / d beta = - kappa_3(beta)` for every `beta > 1`. -/
theorem hasDerivAt_logEnergyVariance
    {β : ℝ} (hβ : 1 < β) :
    HasDerivAt logEnergyVariance (-logEnergyThirdCumulant β) β := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  have hsE : (1 : EReal) < (((β : ℂ).re : ℝ) : EReal) := by
    exact_mod_cast hs
  have habs0 :
      LSeries.abscissaOfAbsConv vonMangoldtComplex < (((β : ℂ).re : ℝ) : EReal) :=
    lt_of_le_of_lt abscissa_vonMangoldtComplex_le_one hsE
  have habs :
      LSeries.abscissaOfAbsConv (LSeries.logMul vonMangoldtComplex) <
        (((β : ℂ).re : ℝ) : EReal) := by
    simpa using habs0
  have hc := LSeries_hasDerivAt habs
  have hr : HasDerivAt
      (fun x : ℝ =>
        (LSeries (LSeries.logMul vonMangoldtComplex) (x : ℂ)).re)
      (-(LSeries (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) (β : ℂ))).re β :=
    hc.real_of_complex
  have hcoef :
      (-(LSeries (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) (β : ℂ))).re =
        -logEnergyThirdCumulant β := by
    simp only [Complex.neg_re]
    rw [logMul_logMul_vonMangoldt_re_eq_thirdCumulant hβ]
  rw [hcoef] at hr
  have heq :
      (fun x : ℝ => logEnergyVariance x) =ᶠ[𝓝 β]
        (fun x : ℝ =>
          (LSeries (LSeries.logMul vonMangoldtComplex) (x : ℂ)).re) := by
    filter_upwards [Ioi_mem_nhds hβ] with x hx
    exact logEnergyVariance_eq_logMul_re hx
  exact hr.congr_of_eventuallyEq heq

/-- Consequently the variance derivative is strictly negative on `beta > 1`. -/
theorem deriv_logEnergyVariance_neg
    {β : ℝ} (hβ : 1 < β) :
    deriv logEnergyVariance β < 0 := by
  rw [(hasDerivAt_logEnergyVariance hβ).deriv]
  exact neg_lt_zero.mpr (logEnergyThirdCumulant_pos hβ)

end GppZetaGibbsCumulantDerivative

#print axioms GppZetaGibbsCumulantDerivative.logEnergyVariance_eq_logMul_re
#print axioms GppZetaGibbsCumulantDerivative.logMul_logMul_vonMangoldt_re_eq_thirdCumulant
#print axioms GppZetaGibbsCumulantDerivative.hasDerivAt_logEnergyVariance
#print axioms GppZetaGibbsCumulantDerivative.deriv_logEnergyVariance_neg
