import GppVerify.RiemannHypothesis.ZetaGibbsThermodynamicDerivatives
import Mathlib.Tactic

/-!
# Continuity of the zeta Gibbs Fisher metric on the honest half-line

The genuine Gibbs variance is identified pointwise on `β>1` with the real part of an
explicit quotient of zeta and its first two derivatives.  Analyticity of zeta and
nonvanishing in the half-plane therefore give the local continuity required by the
strict KL-orientation integral argument.
-/

namespace GppZetaGibbsFisherContinuity

open Complex Set
open GppZetaGibbsMoments
open GppZetaGibbsFisher
open GppZetaThirdCumulantStrict

/-- The real part of the explicit zeta Fisher response is continuous at every `β>1`. -/
theorem continuousAt_zetaVarianceResponse_re
    {β : ℝ} (hβ : 1 < β) :
    ContinuousAt (fun x : ℝ => (zetaVarianceResponse x).re) β := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  have hsset : (β : ℂ) ∈ zetaHalfPlane := hs
  have hc0 : ContinuousAt riemannZeta (β : ℂ) :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane (β : ℂ) hsset).continuousAt
  have hc1 : ContinuousAt (deriv riemannZeta) (β : ℂ) :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane.deriv (β : ℂ) hsset).continuousAt
  have hc2 : ContinuousAt (deriv (deriv riemannZeta)) (β : ℂ) :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane.deriv.deriv (β : ℂ) hsset).continuousAt
  have hne : riemannZeta (β : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_right_half_plane hs
  have hc : ContinuousAt
      (fun s : ℂ =>
        deriv (deriv riemannZeta) s / riemannZeta s -
          (deriv riemannZeta s / riemannZeta s) ^ 2)
      (β : ℂ) := by
    exact (hc2.div hc0 hne).sub ((hc1.div hc0 hne).pow 2)
  have hcomp : ContinuousAt
      (fun x : ℝ =>
        (deriv (deriv riemannZeta) (x : ℂ) / riemannZeta (x : ℂ) -
          (deriv riemannZeta (x : ℂ) / riemannZeta (x : ℂ)) ^ 2).re)
      β := by
    exact Complex.continuous_re.continuousAt.comp β
      (hc.comp β Complex.continuous_ofReal.continuousAt)
  simpa [zetaVarianceResponse, iteratedDeriv_succ', iteratedDeriv_one] using hcomp

/-- The actual Gibbs Fisher metric is continuous on every compact interval contained
in the honest Gibbs half-line. -/
theorem logEnergyVariance_continuousOn_Icc
    {β γ : ℝ} (hβ : 1 < β) (hβγ : β ≤ γ) :
    ContinuousOn logEnergyVariance (Icc β γ) := by
  let f : ℝ → ℝ := fun x => (zetaVarianceResponse x).re
  have hf : ContinuousOn f (Icc β γ) := by
    intro x hx
    have hx1 : 1 < x := lt_of_lt_of_le hβ hx.1
    exact (continuousAt_zetaVarianceResponse_re hx1).continuousWithinAt
  apply hf.congr
  intro x hx
  have hx1 : 1 < x := lt_of_lt_of_le hβ hx.1
  dsimp [f]
  rw [zetaVarianceResponse_eq_ofReal_logEnergyVariance hx1]
  simp

end GppZetaGibbsFisherContinuity

#print axioms GppZetaGibbsFisherContinuity.continuousAt_zetaVarianceResponse_re
#print axioms GppZetaGibbsFisherContinuity.logEnergyVariance_continuousOn_Icc
