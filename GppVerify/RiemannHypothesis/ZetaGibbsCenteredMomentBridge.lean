import GppVerify.RiemannHypothesis.ZetaGibbsTwoObservableStrict
import GppVerify.RiemannHypothesis.ZetaGibbsCumulantHierarchy
import Mathlib.Tactic

/-!
# Raw-moment bridge for the strict zeta Gibbs determinant

The strict centered covariance determinant is proved independently in
`ZetaGibbsTwoObservableStrict`.  This file identifies its three covariance
coefficients with the raw-moment quantities already used by the zeta Gibbs
cumulant hierarchy.  Consequently the existing exact cumulant formula

  D_beta = kappa_2*kappa_4 + 2*kappa_2^3 - kappa_3^2

inherits strict positivity on the honest Gibbs half-line `beta > 1`.
No analytic continuation is used.
-/

namespace GppZetaGibbsCenteredMomentBridge

open GppZetaGibbsSummability
open GppZetaGibbsFisher
open GppZetaGibbsFourthCumulant
open GppZetaGibbsCumulantHierarchy
open GppZetaGibbsTwoObservableStrict

/-- The normalized Gibbs probabilities sum to one on the honest Gibbs domain. -/
theorem gibbsProbability_tsum_eq_one {beta : ℝ} (hbeta : 1 < beta) :
    (∑' n : ℕ, gibbsProbability beta n) = 1 := by
  have hZ : Z beta ≠ 0 := by
    exact (show 0 < Z beta by simpa [Z] using gibbsWeight_tsum_pos hbeta).ne'
  calc
    (∑' n : ℕ, gibbsProbability beta n) =
        ∑' n : ℕ, gibbsWeight beta n / Z beta := by rfl
    _ = (∑' n : ℕ, gibbsWeight beta n) / Z beta := by
      rw [tsum_div_const]
    _ = Z beta / Z beta := by rfl
    _ = 1 := div_self hZ

/-- First normalized raw log-energy moment. -/
theorem gibbsProbability_firstMoment {beta : ℝ} :
    (∑' n : ℕ, gibbsProbability beta n * logEnergy n) = M1 beta / Z beta := by
  calc
    (∑' n : ℕ, gibbsProbability beta n * logEnergy n) =
        ∑' n : ℕ, (gibbsWeight beta n * logEnergy n) / Z beta := by
      apply tsum_congr
      intro n
      unfold gibbsProbability
      ring
    _ = (∑' n : ℕ, gibbsWeight beta n * logEnergy n) / Z beta := by
      rw [tsum_div_const]
    _ = M1 beta / Z beta := by rfl

/-- Second normalized raw log-energy moment. -/
theorem gibbsProbability_secondMoment {beta : ℝ} :
    (∑' n : ℕ, gibbsProbability beta n * (logEnergy n) ^ 2) = M2 beta / Z beta := by
  calc
    (∑' n : ℕ, gibbsProbability beta n * (logEnergy n) ^ 2) =
        ∑' n : ℕ, (gibbsWeight beta n * (logEnergy n) ^ 2) / Z beta := by
      apply tsum_congr
      intro n
      unfold gibbsProbability
      ring
    _ = (∑' n : ℕ, gibbsWeight beta n * (logEnergy n) ^ 2) / Z beta := by
      rw [tsum_div_const]
    _ = M2 beta / Z beta := by rfl

/-- Third normalized raw log-energy moment. -/
theorem gibbsProbability_thirdMoment {beta : ℝ} :
    (∑' n : ℕ, gibbsProbability beta n * (logEnergy n) ^ 3) = M3 beta / Z beta := by
  calc
    (∑' n : ℕ, gibbsProbability beta n * (logEnergy n) ^ 3) =
        ∑' n : ℕ, (gibbsWeight beta n * (logEnergy n) ^ 3) / Z beta := by
      apply tsum_congr
      intro n
      unfold gibbsProbability
      ring
    _ = (∑' n : ℕ, gibbsWeight beta n * (logEnergy n) ^ 3) / Z beta := by
      rw [tsum_div_const]
    _ = M3 beta / Z beta := by rfl

/-- Fourth normalized raw log-energy moment. -/
theorem gibbsProbability_fourthMoment {beta : ℝ} :
    (∑' n : ℕ, gibbsProbability beta n * (logEnergy n) ^ 4) = M4 beta / Z beta := by
  calc
    (∑' n : ℕ, gibbsProbability beta n * (logEnergy n) ^ 4) =
        ∑' n : ℕ, (gibbsWeight beta n * (logEnergy n) ^ 4) / Z beta := by
      apply tsum_congr
      intro n
      unfold gibbsProbability
      ring
    _ = (∑' n : ℕ, gibbsWeight beta n * (logEnergy n) ^ 4) / Z beta := by
      rw [tsum_div_const]
    _ = M4 beta / Z beta := by rfl

private theorem summable_prob_zero {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ => gibbsProbability beta n) := by
  have h := (summable_gibbsWeight hbeta).div_const (Z beta)
  exact h.congr (fun n => by rfl)

private theorem summable_prob_one {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ => gibbsProbability beta n * logEnergy n) := by
  have h := (summable_gibbsWeight_mul_logEnergy hbeta).div_const (Z beta)
  refine h.congr ?_
  intro n
  unfold gibbsProbability
  ring

private theorem summable_prob_two {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ => gibbsProbability beta n * (logEnergy n) ^ 2) := by
  have h := (summable_gibbsWeight_mul_logEnergy_sq hbeta).div_const (Z beta)
  refine h.congr ?_
  intro n
  unfold gibbsProbability
  ring

private theorem summable_prob_three {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ => gibbsProbability beta n * (logEnergy n) ^ 3) := by
  have h := (summable_gibbsWeight_mul_logEnergy_cube hbeta).div_const (Z beta)
  refine h.congr ?_
  intro n
  unfold gibbsProbability
  ring

private theorem summable_prob_four {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ => gibbsProbability beta n * (logEnergy n) ^ 4) := by
  have h := (summable_gibbsWeight_mul_logEnergy_fourth hbeta).div_const (Z beta)
  refine h.congr ?_
  intro n
  unfold gibbsProbability
  ring

/-- The centered variance coefficient is exactly the existing zeta Gibbs variance. -/
theorem centeredLogVariance_eq_logEnergyVariance
    {beta : ℝ} (hbeta : 1 < beta) :
    centeredLogVariance beta = logEnergyVariance beta := by
  let mu : ℝ := M1 beta / Z beta
  have h2 := summable_prob_two hbeta
  have h1 := summable_prob_one hbeta
  have h0 := summable_prob_zero hbeta
  have h1c := h1.mul_left (-2 * mu)
  have h0c := h0.mul_left (mu ^ 2)
  calc
    centeredLogVariance beta =
        ∑' n : ℕ,
          gibbsProbability beta n * (logEnergy n) ^ 2 +
          (-2 * mu) * (gibbsProbability beta n * logEnergy n) +
          (mu ^ 2) * gibbsProbability beta n := by
      unfold centeredLogVariance centeredLogEnergy
      apply tsum_congr
      intro n
      dsimp [mu]
      ring
    _ =
        (∑' n : ℕ, gibbsProbability beta n * (logEnergy n) ^ 2) +
        (-2 * mu) * (∑' n : ℕ, gibbsProbability beta n * logEnergy n) +
        (mu ^ 2) * (∑' n : ℕ, gibbsProbability beta n) := by
      rw [tsum_add (h2.add h1c) h0c, tsum_add h2 h1c]
      simp only [tsum_mul_left]
    _ = M2 beta / Z beta + (-2 * mu) * (M1 beta / Z beta) + mu ^ 2 := by
      rw [gibbsProbability_secondMoment, gibbsProbability_firstMoment,
        gibbsProbability_tsum_eq_one hbeta]
      ring
    _ = logEnergyVariance beta := by
      unfold logEnergyVariance
      dsimp [mu]
      ring

/-- The centered mixed coefficient is exactly `Cov(X,X^2)`. -/
theorem centeredLogSquareCovariance_eq
    {beta : ℝ} (hbeta : 1 < beta) :
    centeredLogSquareCovariance beta = logEnergySquareCovariance beta := by
  let mu : ℝ := M1 beta / Z beta
  let nu : ℝ := M2 beta / Z beta
  have h3 := summable_prob_three hbeta
  have h2 := summable_prob_two hbeta
  have h1 := summable_prob_one hbeta
  have h0 := summable_prob_zero hbeta
  have h2c := h2.mul_left (-mu)
  have h1c := h1.mul_left (-nu)
  have h0c := h0.mul_left (mu * nu)
  calc
    centeredLogSquareCovariance beta =
        ∑' n : ℕ,
          gibbsProbability beta n * (logEnergy n) ^ 3 +
          (-mu) * (gibbsProbability beta n * (logEnergy n) ^ 2) +
          (-nu) * (gibbsProbability beta n * logEnergy n) +
          (mu * nu) * gibbsProbability beta n := by
      unfold centeredLogSquareCovariance centeredLogEnergy centeredLogEnergySq
      apply tsum_congr
      intro n
      dsimp [mu, nu]
      ring
    _ =
        (∑' n : ℕ, gibbsProbability beta n * (logEnergy n) ^ 3) +
        (-mu) * (∑' n : ℕ, gibbsProbability beta n * (logEnergy n) ^ 2) +
        (-nu) * (∑' n : ℕ, gibbsProbability beta n * logEnergy n) +
        (mu * nu) * (∑' n : ℕ, gibbsProbability beta n) := by
      rw [tsum_add (((h3.add h2c).add h1c)) h0c,
        tsum_add (h3.add h2c) h1c, tsum_add h3 h2c]
      simp only [tsum_mul_left]
    _ = M3 beta / Z beta + (-mu) * (M2 beta / Z beta) +
        (-nu) * (M1 beta / Z beta) + mu * nu := by
      rw [gibbsProbability_thirdMoment, gibbsProbability_secondMoment,
        gibbsProbability_firstMoment, gibbsProbability_tsum_eq_one hbeta]
      ring
    _ = logEnergySquareCovariance beta := by
      unfold logEnergySquareCovariance
      dsimp [mu, nu]
      ring

/-- The centered squared-observable variance is exactly the existing raw-moment form. -/
theorem centeredLogSquareVariance_eq
    {beta : ℝ} (hbeta : 1 < beta) :
    centeredLogSquareVariance beta = logEnergySquareVariance beta := by
  let nu : ℝ := M2 beta / Z beta
  have h4 := summable_prob_four hbeta
  have h2 := summable_prob_two hbeta
  have h0 := summable_prob_zero hbeta
  have h2c := h2.mul_left (-2 * nu)
  have h0c := h0.mul_left (nu ^ 2)
  calc
    centeredLogSquareVariance beta =
        ∑' n : ℕ,
          gibbsProbability beta n * (logEnergy n) ^ 4 +
          (-2 * nu) * (gibbsProbability beta n * (logEnergy n) ^ 2) +
          (nu ^ 2) * gibbsProbability beta n := by
      unfold centeredLogSquareVariance centeredLogEnergySq
      apply tsum_congr
      intro n
      dsimp [nu]
      ring
    _ =
        (∑' n : ℕ, gibbsProbability beta n * (logEnergy n) ^ 4) +
        (-2 * nu) * (∑' n : ℕ, gibbsProbability beta n * (logEnergy n) ^ 2) +
        (nu ^ 2) * (∑' n : ℕ, gibbsProbability beta n) := by
      rw [tsum_add (h4.add h2c) h0c, tsum_add h4 h2c]
      simp only [tsum_mul_left]
    _ = M4 beta / Z beta + (-2 * nu) * (M2 beta / Z beta) + nu ^ 2 := by
      rw [gibbsProbability_fourthMoment, gibbsProbability_secondMoment,
        gibbsProbability_tsum_eq_one hbeta]
      ring
    _ = logEnergySquareVariance beta := by
      unfold logEnergySquareVariance
      dsimp [nu]
      ring

/-- The strictly positive centered determinant is exactly the cumulant-hierarchy
two-observable determinant. -/
theorem centeredCovarianceDet_eq_logEnergyTwoObservableDet
    {beta : ℝ} (hbeta : 1 < beta) :
    centeredLogVariance beta * centeredLogSquareVariance beta -
      (centeredLogSquareCovariance beta) ^ 2 =
      logEnergyTwoObservableDet beta := by
  rw [centeredLogVariance_eq_logEnergyVariance hbeta,
    centeredLogSquareVariance_eq hbeta,
    centeredLogSquareCovariance_eq hbeta]
  rfl

/-- **Strict two-observable zeta Gibbs determinant.** -/
theorem logEnergyTwoObservableDet_pos
    {beta : ℝ} (hbeta : 1 < beta) :
    0 < logEnergyTwoObservableDet beta := by
  rw [← centeredCovarianceDet_eq_logEnergyTwoObservableDet hbeta]
  exact centeredCovarianceDet_pos hbeta

/-- **Strict cumulant determinant inequality on the honest Gibbs half-line.** -/
theorem cumulant_fluctuation_invariant_pos
    {beta : ℝ} (hbeta : 1 < beta) :
    0 < logEnergyVariance beta * logEnergyFourthCumulant beta +
      2 * (logEnergyVariance beta) ^ 3 -
      (logEnergyThirdCumulant beta) ^ 2 := by
  rw [← logEnergyTwoObservableDet_eq_cumulants beta]
  exact logEnergyTwoObservableDet_pos hbeta

end GppZetaGibbsCenteredMomentBridge

#print axioms GppZetaGibbsCenteredMomentBridge.centeredLogVariance_eq_logEnergyVariance
#print axioms GppZetaGibbsCenteredMomentBridge.centeredLogSquareCovariance_eq
#print axioms GppZetaGibbsCenteredMomentBridge.centeredLogSquareVariance_eq
#print axioms GppZetaGibbsCenteredMomentBridge.logEnergyTwoObservableDet_pos
#print axioms GppZetaGibbsCenteredMomentBridge.cumulant_fluctuation_invariant_pos
