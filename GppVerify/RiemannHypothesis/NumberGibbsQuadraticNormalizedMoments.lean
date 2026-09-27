import GppVerify.RiemannHypothesis.NumberGibbsQuadraticThermodynamics
import Mathlib.Tactic

/-!
# Normalized raw moments for the quadratically confined number Gibbs family

This file gives the actual countable probability normalization and normalized
raw log-energy moments through order six. It is the analytic API needed for
the final centered sixth-order `tsum` expansion in the curvature proof.
-/

namespace GppNumberGibbsQuadraticNormalizedMoments

open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticConfinement
open GppNumberGibbsQuadraticThermodynamics
open GppZetaGibbsSummability

/-- Normalized probability mass of the confined number Gibbs family. -/
noncomputable def probability (β η : ℝ) (n : ℕ) : ℝ :=
  numberGibbsWeight β η n / Z β η

/-- The normalized probabilities sum to one on `η > 0`. -/
theorem probability_tsum_eq_one
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    (∑' n : ℕ, probability β η n) = 1 := by
  have hZ : Z β η ≠ 0 := (Z_pos β hη).ne'
  calc
    (∑' n : ℕ, probability β η n) =
        ∑' n : ℕ, numberGibbsWeight β η n / Z β η := by rfl
    _ = (∑' n : ℕ, numberGibbsWeight β η n) / Z β η := by
      rw [tsum_div_const]
    _ = Z β η / Z β η := by rfl
    _ = 1 := div_self hZ

/-- First normalized raw log-energy moment. -/
theorem probability_firstMoment (β η : ℝ) :
    (∑' n : ℕ, probability β η n * numberLogEnergy n) = M1 β η / Z β η := by
  calc
    (∑' n : ℕ, probability β η n * numberLogEnergy n) =
        ∑' n : ℕ, (numberGibbsWeight β η n * numberLogEnergy n) / Z β η := by
      apply tsum_congr
      intro n
      unfold probability
      ring
    _ = (∑' n : ℕ, numberGibbsWeight β η n * numberLogEnergy n) / Z β η := by
      rw [tsum_div_const]
    _ = M1 β η / Z β η := by rfl

/-- Second normalized raw log-energy moment. -/
theorem probability_secondMoment (β η : ℝ) :
    (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 2) = M2 β η / Z β η := by
  calc
    (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 2) =
        ∑' n : ℕ, (numberGibbsWeight β η n * numberLogEnergy n ^ 2) / Z β η := by
      apply tsum_congr
      intro n
      unfold probability
      ring
    _ = (∑' n : ℕ, numberGibbsWeight β η n * numberLogEnergy n ^ 2) / Z β η := by
      rw [tsum_div_const]
    _ = M2 β η / Z β η := by rfl

/-- Third normalized raw log-energy moment. -/
theorem probability_thirdMoment (β η : ℝ) :
    (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 3) = M3 β η / Z β η := by
  calc
    (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 3) =
        ∑' n : ℕ, (numberGibbsWeight β η n * numberLogEnergy n ^ 3) / Z β η := by
      apply tsum_congr
      intro n
      unfold probability
      ring
    _ = (∑' n : ℕ, numberGibbsWeight β η n * numberLogEnergy n ^ 3) / Z β η := by
      rw [tsum_div_const]
    _ = M3 β η / Z β η := by rfl

/-- Fourth normalized raw log-energy moment. -/
theorem probability_fourthMoment (β η : ℝ) :
    (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 4) = M4 β η / Z β η := by
  calc
    (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 4) =
        ∑' n : ℕ, (numberGibbsWeight β η n * numberLogEnergy n ^ 4) / Z β η := by
      apply tsum_congr
      intro n
      unfold probability
      ring
    _ = (∑' n : ℕ, numberGibbsWeight β η n * numberLogEnergy n ^ 4) / Z β η := by
      rw [tsum_div_const]
    _ = M4 β η / Z β η := by rfl

/-- Fifth normalized raw log-energy moment. -/
theorem probability_fifthMoment (β η : ℝ) :
    (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 5) = M5 β η / Z β η := by
  calc
    (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 5) =
        ∑' n : ℕ, (numberGibbsWeight β η n * numberLogEnergy n ^ 5) / Z β η := by
      apply tsum_congr
      intro n
      unfold probability
      ring
    _ = (∑' n : ℕ, numberGibbsWeight β η n * numberLogEnergy n ^ 5) / Z β η := by
      rw [tsum_div_const]
    _ = M5 β η / Z β η := by rfl

/-- Sixth normalized raw log-energy moment. -/
theorem probability_sixthMoment (β η : ℝ) :
    (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 6) = M6 β η / Z β η := by
  calc
    (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 6) =
        ∑' n : ℕ, (numberGibbsWeight β η n * numberLogEnergy n ^ 6) / Z β η := by
      apply tsum_congr
      intro n
      unfold probability
      ring
    _ = (∑' n : ℕ, numberGibbsWeight β η n * numberLogEnergy n ^ 6) / Z β η := by
      rw [tsum_div_const]
    _ = M6 β η / Z β η := by rfl

/-- Normalized probability weights are summable. -/
theorem summable_probability (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ => probability β η n) := by
  have h := (summable_numberGibbsWeight β hη).div_const (Z β η)
  exact h.congr (fun n => by rfl)

/-- Normalized first-moment integrand is summable. -/
theorem summable_probability_one (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ => probability β η n * numberLogEnergy n) := by
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz1 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 1) := by
    simpa using summable_gibbsWeight_mul_logEnergy htwo
  have hraw := summable_numberGibbs_moment_of_quadratic β η 1 hη hz1
  have h := hraw.div_const (Z β η)
  refine h.congr ?_
  intro n
  unfold probability
  ring

/-- Normalized second-moment integrand is summable. -/
theorem summable_probability_two (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ => probability β η n * numberLogEnergy n ^ 2) := by
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz2 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 2) :=
    summable_gibbsWeight_mul_logEnergy_sq htwo
  have hraw := summable_numberGibbs_moment_of_quadratic β η 2 hη hz2
  have h := hraw.div_const (Z β η)
  refine h.congr ?_
  intro n
  unfold probability
  ring

/-- Normalized third-moment integrand is summable. -/
theorem summable_probability_three (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ => probability β η n * numberLogEnergy n ^ 3) := by
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz3 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 3) :=
    summable_gibbsWeight_mul_logEnergy_cube htwo
  have hraw := summable_numberGibbs_moment_of_quadratic β η 3 hη hz3
  have h := hraw.div_const (Z β η)
  refine h.congr ?_
  intro n
  unfold probability
  ring

/-- Normalized fourth-moment integrand is summable. -/
theorem summable_probability_four (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ => probability β η n * numberLogEnergy n ^ 4) := by
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz4 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 4) :=
    summable_gibbsWeight_mul_logEnergy_fourth htwo
  have hraw := summable_numberGibbs_moment_of_quadratic β η 4 hη hz4
  have h := hraw.div_const (Z β η)
  refine h.congr ?_
  intro n
  unfold probability
  ring

/-- Normalized fifth-moment integrand is summable. -/
theorem summable_probability_five (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ => probability β η n * numberLogEnergy n ^ 5) := by
  have h := (summable_M5_integrand β hη).div_const (Z β η)
  refine h.congr ?_
  intro n
  unfold probability
  ring

/-- Normalized sixth-moment integrand is summable. -/
theorem summable_probability_six (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ => probability β η n * numberLogEnergy n ^ 6) := by
  have h := (summable_M6_integrand β hη).div_const (Z β η)
  refine h.congr ?_
  intro n
  unfold probability
  ring

end GppNumberGibbsQuadraticNormalizedMoments

#print axioms GppNumberGibbsQuadraticNormalizedMoments.probability_tsum_eq_one
#print axioms GppNumberGibbsQuadraticNormalizedMoments.probability_firstMoment
#print axioms GppNumberGibbsQuadraticNormalizedMoments.probability_sixthMoment
#print axioms GppNumberGibbsQuadraticNormalizedMoments.summable_probability
#print axioms GppNumberGibbsQuadraticNormalizedMoments.summable_probability_six