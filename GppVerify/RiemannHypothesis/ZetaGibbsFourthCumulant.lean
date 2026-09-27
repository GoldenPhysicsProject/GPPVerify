import GppVerify.RiemannHypothesis.ZetaGibbsFisher
import Mathlib.Tactic

/-!
# Fourth cumulant of the zeta Gibbs family

The first four logarithmic coefficient insertions of the constant-one L-series are
already identified with the first four real Gibbs raw moments.  This file assembles
the genuine fourth central cumulant and identifies it exactly with the fourth
logarithmic derivative response of zeta on the honest Gibbs half-plane `β > 1`.

No sign claim for the fourth cumulant is made here.
-/

namespace GppZetaGibbsFourthCumulant

open Complex LSeries
open GppZetaGibbsSummability
open GppZetaGibbsMoments
open GppZetaGibbsMomentBridge
open GppZetaGibbsFisher

/-- Unnormalized fourth log-energy moment. -/
noncomputable def M4 (β : ℝ) : ℝ :=
  ∑' n, gibbsWeight β n * (logEnergy n) ^ 4

/-- Genuine fourth cumulant of the Gibbs log-energy distribution, written in
terms of normalized raw moments. -/
noncomputable def logEnergyFourthCumulant (β : ℝ) : ℝ :=
  M4 β / Z β -
    4 * (M3 β / Z β) * (M1 β / Z β) -
    3 * (M2 β / Z β) ^ 2 +
    12 * (M2 β / Z β) * (M1 β / Z β) ^ 2 -
    6 * (M1 β / Z β) ^ 4

/-- Fourth logarithmic derivative response of zeta, expressed without invoking
`Complex.log`. -/
noncomputable def zetaFourthCumulantResponse (β : ℝ) : ℂ :=
  iteratedDeriv 4 riemannZeta (β : ℂ) / riemannZeta (β : ℂ) -
    4 * (iteratedDeriv 3 riemannZeta (β : ℂ) / riemannZeta (β : ℂ)) *
      (deriv riemannZeta (β : ℂ) / riemannZeta (β : ℂ)) -
    3 * (iteratedDeriv 2 riemannZeta (β : ℂ) / riemannZeta (β : ℂ)) ^ 2 +
    12 * (iteratedDeriv 2 riemannZeta (β : ℂ) / riemannZeta (β : ℂ)) *
      (deriv riemannZeta (β : ℂ) / riemannZeta (β : ℂ)) ^ 2 -
    6 * (deriv riemannZeta (β : ℂ) / riemannZeta (β : ℂ)) ^ 4

/-- The fourth logarithmic zeta response is exactly the embedded genuine fourth
Gibbs cumulant on `β > 1`. -/
theorem zetaFourthCumulantResponse_eq_ofReal_logEnergyFourthCumulant
    {β : ℝ} (hβ : 1 < β) :
    zetaFourthCumulantResponse β = (logEnergyFourthCumulant β : ℂ) := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  rw [zetaFourthCumulantResponse, logEnergyFourthCumulant, M4, M3, M2, M1, Z]
  rw [iteratedDeriv_four_riemannZeta_eq_logFourthMomentLSeries hs]
  rw [LSeries_logMul_four_one_eq_ofReal_fourthMoment hβ]
  rw [iteratedDeriv_three_riemannZeta_eq_neg_logCubeMomentLSeries hs]
  rw [LSeries_logMul_logMul_logMul_one_eq_ofReal_thirdMoment hβ]
  rw [iteratedDeriv_two_riemannZeta_eq_logSqMomentLSeries hs]
  rw [LSeries_logMul_logMul_one_eq_ofReal_secondMoment hβ]
  rw [deriv_riemannZeta_eq_neg_logMomentLSeries hs]
  rw [LSeries_logMul_one_eq_ofReal_firstMoment hβ]
  rw [riemannZeta_eq_LSeries_one hs]
  rw [LSeries_one_eq_ofReal_gibbsWeight_tsum hβ]
  norm_cast
  ring

/-- The fourth cumulant response lies on the real axis throughout the honest
Gibbs domain. -/
theorem zetaFourthCumulantResponse_im_eq_zero
    {β : ℝ} (hβ : 1 < β) :
    (zetaFourthCumulantResponse β).im = 0 := by
  rw [zetaFourthCumulantResponse_eq_ofReal_logEnergyFourthCumulant hβ]
  simp

end GppZetaGibbsFourthCumulant

#print axioms GppZetaGibbsFourthCumulant.zetaFourthCumulantResponse_eq_ofReal_logEnergyFourthCumulant
#print axioms GppZetaGibbsFourthCumulant.zetaFourthCumulantResponse_im_eq_zero
