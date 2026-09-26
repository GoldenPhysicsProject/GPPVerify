import GppVerify.RiemannHypothesis.ZetaGibbsCumulantDerivative
import GppVerify.RiemannHypothesis.VonMangoldtQuarticPositivity
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
# Third-cumulant differential law for the zeta Gibbs family

On the honest Gibbs half-line `beta > 1`, the genuine third cumulant is already
identified with the real part of the twice-logarithm-weighted von Mangoldt L-series.
Differentiating that absolutely convergent L-series inserts one further logarithm
and a minus sign. Therefore

  d/d beta kappa_3(beta)
    = - Re L((logMul)^3 Lambda, beta) < 0.

This proves strict decrease of the genuine third Gibbs cumulant without yet calling
the three-log arithmetic response `kappa_4`.  The separate raw-moment identity
identifying that response with the genuine fourth central cumulant remains a
formalization target.
-/

namespace GppZetaGibbsThirdCumulantDerivative

open Complex LSeries Set Filter
open GppGlobalVonMangoldt
open GppVonMangoldtCumulantSummability
open GppVonMangoldtQuarticPositivity
open GppZetaGibbsFisher
open GppZetaGibbsCumulantDerivative
open scoped LSeries.notation ArithmeticFunction Topology

/-- Exact derivative of the genuine third Gibbs cumulant: one further logarithmic
von Mangoldt insertion with the canonical minus sign. -/
theorem hasDerivAt_logEnergyThirdCumulant
    {β : ℝ} (hβ : 1 < β) :
    HasDerivAt logEnergyThirdCumulant
      (-(LSeries
        (LSeries.logMul (LSeries.logMul (LSeries.logMul vonMangoldtComplex)))
        (β : ℂ)).re) β := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  have hsE : (1 : EReal) < (((β : ℂ).re : ℝ) : EReal) := by
    exact_mod_cast hs
  have habs0 :
      LSeries.abscissaOfAbsConv vonMangoldtComplex < (((β : ℂ).re : ℝ) : EReal) :=
    lt_of_le_of_lt abscissa_vonMangoldtComplex_le_one hsE
  have habs :
      LSeries.abscissaOfAbsConv
          (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) <
        (((β : ℂ).re : ℝ) : EReal) := by
    simpa using habs0
  have hc := LSeries_hasDerivAt habs
  have hr : HasDerivAt
      (fun x : ℝ =>
        (LSeries
          (LSeries.logMul (LSeries.logMul vonMangoldtComplex))
          (x : ℂ)).re)
      (-(LSeries
        (LSeries.logMul (LSeries.logMul (LSeries.logMul vonMangoldtComplex)))
        (β : ℂ))).re β :=
    hc.real_of_complex
  have hcoef :
      (-(LSeries
        (LSeries.logMul (LSeries.logMul (LSeries.logMul vonMangoldtComplex)))
        (β : ℂ))).re =
      -(LSeries
        (LSeries.logMul (LSeries.logMul (LSeries.logMul vonMangoldtComplex)))
        (β : ℂ)).re := by
    simp
  rw [hcoef] at hr
  have heq :
      (fun x : ℝ => logEnergyThirdCumulant x) =ᶠ[𝓝 β]
        (fun x : ℝ =>
          (LSeries
            (LSeries.logMul (LSeries.logMul vonMangoldtComplex))
            (x : ℂ)).re) := by
    filter_upwards [Ioi_mem_nhds hβ] with x hx
    exact (logMul_logMul_vonMangoldt_re_eq_thirdCumulant hx).symm
  exact hr.congr_of_eventuallyEq heq

/-- The genuine third cumulant is strictly decreasing throughout the honest Gibbs
domain. -/
theorem deriv_logEnergyThirdCumulant_neg
    {β : ℝ} (hβ : 1 < β) :
    deriv logEnergyThirdCumulant β < 0 := by
  rw [(hasDerivAt_logEnergyThirdCumulant hβ).deriv]
  exact neg_lt_zero.mpr (logMul_three_vonMangoldt_re_pos hβ)

end GppZetaGibbsThirdCumulantDerivative

#print axioms GppZetaGibbsThirdCumulantDerivative.hasDerivAt_logEnergyThirdCumulant
#print axioms GppZetaGibbsThirdCumulantDerivative.deriv_logEnergyThirdCumulant_neg
