import GppVerify.RiemannHypothesis.ZetaGibbsCumulantHierarchy
import GppVerify.RiemannHypothesis.StrictQuadraticDeterminant
import Mathlib.Tactic

/-!
# Strict two-observable zeta Gibbs fluctuation determinant

For beta > 1, normalize the Gibbs weights by Z(beta), center the observables
X = log(n+1) and X^2, and consider every nonzero linear combination of those
centered observables. Fourth-moment summability makes the corresponding
probability-weighted square summable. Strict positivity is witnessed already by
the first three states n=0,1,2: a nonzero quadratic score cannot vanish at the
three distinct log-energies 0, log 2, log 3.
-/

namespace GppZetaGibbsTwoObservableStrict

open GppZetaGibbsSummability
open GppZetaGibbsFisher
open GppZetaGibbsFourthCumulant
open GppZetaGibbsCumulantHierarchy
open GppStrictQuadraticDeterminant

noncomputable def gibbsProbability (beta : ℝ) (n : ℕ) : ℝ :=
  gibbsWeight beta n / Z beta

noncomputable def centeredLogEnergy (beta : ℝ) (n : ℕ) : ℝ :=
  logEnergy n - M1 beta / Z beta

noncomputable def centeredLogEnergySq (beta : ℝ) (n : ℕ) : ℝ :=
  (logEnergy n) ^ 2 - M2 beta / Z beta

noncomputable def centeredLogVariance (beta : ℝ) : ℝ :=
  ∑' n : ℕ, gibbsProbability beta n * (centeredLogEnergy beta n) ^ 2

noncomputable def centeredLogSquareCovariance (beta : ℝ) : ℝ :=
  ∑' n : ℕ, gibbsProbability beta n *
    (centeredLogEnergy beta n * centeredLogEnergySq beta n)

noncomputable def centeredLogSquareVariance (beta : ℝ) : ℝ :=
  ∑' n : ℕ, gibbsProbability beta n * (centeredLogEnergySq beta n) ^ 2

private theorem gibbsProbability_pos {beta : ℝ} (hbeta : 1 < beta) (n : ℕ) :
    0 < gibbsProbability beta n := by
  unfold gibbsProbability
  have hw : 0 < gibbsWeight beta n := by
    unfold gibbsWeight
    positivity
  have hZ : 0 < Z beta := by
    simpa [Z] using gibbsWeight_tsum_pos hbeta
  exact div_pos hw hZ

private theorem summable_prob_centeredLog_sq
    {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ =>
      gibbsProbability beta n * (centeredLogEnergy beta n) ^ 2) := by
  let mu : ℝ := M1 beta / Z beta
  have h2 := (summable_gibbsWeight_mul_logEnergy_sq hbeta).div_const (Z beta)
  have h1 := (summable_gibbsWeight_mul_logEnergy hbeta).div_const (Z beta)
  have h0 := (summable_gibbsWeight hbeta).div_const (Z beta)
  have h := h2.add ((h1.mul_left (-2 * mu)).add (h0.mul_left (mu ^ 2)))
  refine h.congr ?_
  intro n
  unfold gibbsProbability centeredLogEnergy
  dsimp [mu]
  ring

private theorem summable_prob_centeredCross
    {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ =>
      gibbsProbability beta n *
        (centeredLogEnergy beta n * centeredLogEnergySq beta n)) := by
  let mu : ℝ := M1 beta / Z beta
  let nu : ℝ := M2 beta / Z beta
  have h3 := (summable_gibbsWeight_mul_logEnergy_cube hbeta).div_const (Z beta)
  have h2 := (summable_gibbsWeight_mul_logEnergy_sq hbeta).div_const (Z beta)
  have h1 := (summable_gibbsWeight_mul_logEnergy hbeta).div_const (Z beta)
  have h0 := (summable_gibbsWeight hbeta).div_const (Z beta)
  have h := h3.add
    ((h2.mul_left (-mu)).add
      ((h1.mul_left (-nu)).add (h0.mul_left (mu * nu))))
  refine h.congr ?_
  intro n
  unfold gibbsProbability centeredLogEnergy centeredLogEnergySq
  dsimp [mu, nu]
  ring

private theorem summable_prob_centeredLogSq_sq
    {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ =>
      gibbsProbability beta n * (centeredLogEnergySq beta n) ^ 2) := by
  let nu : ℝ := M2 beta / Z beta
  have h4 := (summable_gibbsWeight_mul_logEnergy_fourth hbeta).div_const (Z beta)
  have h2 := (summable_gibbsWeight_mul_logEnergy_sq hbeta).div_const (Z beta)
  have h0 := (summable_gibbsWeight hbeta).div_const (Z beta)
  have h := h4.add ((h2.mul_left (-2 * nu)).add (h0.mul_left (nu ^ 2)))
  refine h.congr ?_
  intro n
  unfold gibbsProbability centeredLogEnergySq
  dsimp [nu]
  ring

private theorem three_state_score_nonzero
    {beta a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ n : ℕ,
      a * centeredLogEnergy beta n + b * centeredLogEnergySq beta n ≠ 0 := by
  by_cases h0 :
      a * centeredLogEnergy beta 0 + b * centeredLogEnergySq beta 0 ≠ 0
  · exact ⟨0, h0⟩
  have e0 :
      a * (-(M1 beta / Z beta)) + b * (-(M2 beta / Z beta)) = 0 := by
    simpa [centeredLogEnergy, centeredLogEnergySq, logEnergy] using
      (not_ne_iff.mp h0)
  by_cases h1 :
      a * centeredLogEnergy beta 1 + b * centeredLogEnergySq beta 1 ≠ 0
  · exact ⟨1, h1⟩
  have e1 :
      a * (Real.log 2 - M1 beta / Z beta) +
        b * ((Real.log 2) ^ 2 - M2 beta / Z beta) = 0 := by
    simpa [centeredLogEnergy, centeredLogEnergySq, logEnergy] using
      (not_ne_iff.mp h1)
  by_cases h2 :
      a * centeredLogEnergy beta 2 + b * centeredLogEnergySq beta 2 ≠ 0
  · exact ⟨2, h2⟩
  have e2 :
      a * (Real.log 3 - M1 beta / Z beta) +
        b * ((Real.log 3) ^ 2 - M2 beta / Z beta) = 0 := by
    simpa [centeredLogEnergy, centeredLogEnergySq, logEnergy] using
      (not_ne_iff.mp h2)
  have d2 : a * Real.log 2 + b * (Real.log 2) ^ 2 = 0 := by
    calc
      a * Real.log 2 + b * (Real.log 2) ^ 2 =
          (a * (Real.log 2 - M1 beta / Z beta) +
            b * ((Real.log 2) ^ 2 - M2 beta / Z beta)) -
          (a * (-(M1 beta / Z beta)) + b * (-(M2 beta / Z beta))) := by ring
      _ = 0 := by rw [e1, e0]; ring
  have d3 : a * Real.log 3 + b * (Real.log 3) ^ 2 = 0 := by
    calc
      a * Real.log 3 + b * (Real.log 3) ^ 2 =
          (a * (Real.log 3 - M1 beta / Z beta) +
            b * ((Real.log 3) ^ 2 - M2 beta / Z beta)) -
          (a * (-(M1 beta / Z beta)) + b * (-(M2 beta / Z beta))) := by ring
      _ = 0 := by rw [e2, e0]; ring
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have h23 : Real.log (2 : ℝ) < Real.log 3 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have f2 : Real.log 2 * (a + b * Real.log 2) = 0 := by
    nlinarith [d2]
  have f3 : Real.log 3 * (a + b * Real.log 3) = 0 := by
    nlinarith [d3]
  have ab2 : a + b * Real.log 2 = 0 :=
    (mul_eq_zero.mp f2).resolve_left (ne_of_gt hlog2)
  have ab3 : a + b * Real.log 3 = 0 :=
    (mul_eq_zero.mp f3).resolve_left (ne_of_gt hlog3)
  have hbmul : b * (Real.log 2 - Real.log 3) = 0 := by
    nlinarith [ab2, ab3]
  have hdiff : Real.log 2 - Real.log 3 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_lt h23)
  have hb : b = 0 := (mul_eq_zero.mp hbmul).resolve_right hdiff
  have ha : a = 0 := by simpa [hb] using ab2
  exact False.elim (hab.elim (fun h => h ha) (fun h => h hb))

/-- Every nonzero centered two-observable score has strictly positive normalized
mean square on the honest Gibbs half-line. -/
theorem normalized_centered_quadratic_pos
    {beta a b : ℝ} (hbeta : 1 < beta) (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < ∑' n : ℕ, gibbsProbability beta n *
      (a * centeredLogEnergy beta n + b * centeredLogEnergySq beta n) ^ 2 := by
  have hA := summable_prob_centeredLog_sq hbeta
  have hB := summable_prob_centeredCross hbeta
  have hC := summable_prob_centeredLogSq_sq hbeta
  have hsum : Summable (fun n : ℕ => gibbsProbability beta n *
      (a * centeredLogEnergy beta n + b * centeredLogEnergySq beta n) ^ 2) := by
    have hAa := hA.mul_left (a ^ 2)
    have hBb := hB.mul_left (2 * a * b)
    have hCc := hC.mul_left (b ^ 2)
    refine (hAa.add hBb).add hCc |>.congr ?_
    intro n
    ring
  obtain ⟨n, hn⟩ := three_state_score_nonzero (beta := beta) hab
  have hnonneg : ∀ m : ℕ, 0 ≤ gibbsProbability beta m *
      (a * centeredLogEnergy beta m + b * centeredLogEnergySq beta m) ^ 2 := by
    intro m
    exact mul_nonneg (gibbsProbability_pos hbeta m).le (sq_nonneg _)
  have hterm : 0 < gibbsProbability beta n *
      (a * centeredLogEnergy beta n + b * centeredLogEnergySq beta n) ^ 2 := by
    exact mul_pos (gibbsProbability_pos hbeta n) (sq_pos_of_ne_zero hn)
  exact hsum.tsum_pos hnonneg n hterm

/-- Exact coefficient decomposition of the centered score. -/
theorem normalized_centered_quadratic_eq_covariance
    {beta a b : ℝ} (hbeta : 1 < beta) :
    (∑' n : ℕ, gibbsProbability beta n *
      (a * centeredLogEnergy beta n + b * centeredLogEnergySq beta n) ^ 2) =
      centeredLogVariance beta * a ^ 2 +
        2 * centeredLogSquareCovariance beta * a * b +
        centeredLogSquareVariance beta * b ^ 2 := by
  have hA := summable_prob_centeredLog_sq hbeta
  have hB := summable_prob_centeredCross hbeta
  have hC := summable_prob_centeredLogSq_sq hbeta
  have hAa := hA.mul_left (a ^ 2)
  have hBb := hB.mul_left (2 * a * b)
  have hCc := hC.mul_left (b ^ 2)
  calc
    (∑' n : ℕ, gibbsProbability beta n *
      (a * centeredLogEnergy beta n + b * centeredLogEnergySq beta n) ^ 2) =
        ∑' n : ℕ,
          a ^ 2 * (gibbsProbability beta n * (centeredLogEnergy beta n) ^ 2) +
          (2 * a * b) * (gibbsProbability beta n *
            (centeredLogEnergy beta n * centeredLogEnergySq beta n)) +
          b ^ 2 * (gibbsProbability beta n * (centeredLogEnergySq beta n) ^ 2) := by
            apply tsum_congr
            intro n
            ring
    _ =
        a ^ 2 * centeredLogVariance beta +
          (2 * a * b) * centeredLogSquareCovariance beta +
          b ^ 2 * centeredLogSquareVariance beta := by
            rw [tsum_add (hAa.add hBb) hCc, tsum_add hAa hBb]
            simp [centeredLogVariance, centeredLogSquareCovariance,
              centeredLogSquareVariance]
    _ = centeredLogVariance beta * a ^ 2 +
        2 * centeredLogSquareCovariance beta * a * b +
        centeredLogSquareVariance beta * b ^ 2 := by ring

/-- Strict positivity of the centered covariance determinant. -/
theorem centeredCovarianceDet_pos {beta : ℝ} (hbeta : 1 < beta) :
    0 < centeredLogVariance beta * centeredLogSquareVariance beta -
      (centeredLogSquareCovariance beta) ^ 2 := by
  apply det_pos_of_quadratic_pos
  intro a b hab
  rw [← normalized_centered_quadratic_eq_covariance hbeta]
  exact normalized_centered_quadratic_pos hbeta hab

end GppZetaGibbsTwoObservableStrict

#print axioms GppZetaGibbsTwoObservableStrict.normalized_centered_quadratic_pos
#print axioms GppZetaGibbsTwoObservableStrict.normalized_centered_quadratic_eq_covariance
#print axioms GppZetaGibbsTwoObservableStrict.centeredCovarianceDet_pos
