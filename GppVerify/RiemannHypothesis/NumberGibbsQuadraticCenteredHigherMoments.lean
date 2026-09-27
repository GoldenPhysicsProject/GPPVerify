import GppVerify.RiemannHypothesis.NumberGibbsQuadraticCenteredThirdMoment
import Mathlib.Tactic

/-!
# Higher centered moments for the quadratically confined number Gibbs family

This file completes the countable centered-moment bridge through sixth order.
It identifies the algebraic fourth, fifth, and sixth centered moments with the
honest normalized Gibbs expectations of powers of the centered log-energy.
-/

namespace GppNumberGibbsQuadraticCenteredMoments

open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticNormalizedMoments
open GppNumberGibbsQuadraticCurvatureSquareBridge

/-- The algebraic fourth centered moment is the honest normalized countable
expectation of `(L-⟨L⟩)^4`. -/
theorem probability_centered_fourthMoment
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 4) =
      centralMoment4 β η := by
  let μ : ℝ := M1 β η / Z β η
  have h4 := summable_probability_four β hη
  have h3 := summable_probability_three β hη
  have h2 := summable_probability_two β hη
  have h1 := summable_probability_one β hη
  have h0 := summable_probability β hη
  have h3c := h3.mul_left (-4 * μ)
  have h2c := h2.mul_left (6 * μ ^ 2)
  have h1c := h1.mul_left (-4 * μ ^ 3)
  have h0c := h0.mul_left (μ ^ 4)
  calc
    (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 4) =
        ∑' n : ℕ,
          (probability β η n * numberLogEnergy n ^ 4 +
          (-4 * μ) * (probability β η n * numberLogEnergy n ^ 3) +
          (6 * μ ^ 2) * (probability β η n * numberLogEnergy n ^ 2) +
          (-4 * μ ^ 3) * (probability β η n * numberLogEnergy n) +
          (μ ^ 4) * probability β η n) := by
      apply tsum_congr
      intro n
      unfold centeredLogEnergy internalEnergy
      dsimp [μ]
      ring
    _ = (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 4) +
        (-4 * μ) * (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 3) +
        (6 * μ ^ 2) * (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 2) +
        (-4 * μ ^ 3) * (∑' n : ℕ, probability β η n * numberLogEnergy n) +
        (μ ^ 4) * (∑' n : ℕ, probability β η n) := by
      rw [(((h4.add h3c).add h2c).add h1c).tsum_add h0c,
        ((h4.add h3c).add h2c).tsum_add h1c,
        (h4.add h3c).tsum_add h2c, h4.tsum_add h3c]
      simp only [tsum_mul_left]
    _ = M4 β η / Z β η
        + (-4 * μ) * (M3 β η / Z β η)
        + (6 * μ ^ 2) * (M2 β η / Z β η)
        + (-4 * μ ^ 3) * (M1 β η / Z β η)
        + μ ^ 4 := by
      rw [probability_fourthMoment, probability_thirdMoment,
        probability_secondMoment, probability_firstMoment,
        probability_tsum_eq_one β hη]
      ring
    _ = centralMoment4 β η := by
      unfold centralMoment4
      dsimp [μ]
      ring

/-- The algebraic fifth centered moment is the honest normalized countable
expectation of `(L-⟨L⟩)^5`. -/
theorem probability_centered_fifthMoment
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 5) =
      centralMoment5 β η := by
  let μ : ℝ := M1 β η / Z β η
  have h5 := summable_probability_five β hη
  have h4 := summable_probability_four β hη
  have h3 := summable_probability_three β hη
  have h2 := summable_probability_two β hη
  have h1 := summable_probability_one β hη
  have h0 := summable_probability β hη
  have h4c := h4.mul_left (-5 * μ)
  have h3c := h3.mul_left (10 * μ ^ 2)
  have h2c := h2.mul_left (-10 * μ ^ 3)
  have h1c := h1.mul_left (5 * μ ^ 4)
  have h0c := h0.mul_left (-μ ^ 5)
  calc
    (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 5) =
        ∑' n : ℕ,
          (probability β η n * numberLogEnergy n ^ 5 +
          (-5 * μ) * (probability β η n * numberLogEnergy n ^ 4) +
          (10 * μ ^ 2) * (probability β η n * numberLogEnergy n ^ 3) +
          (-10 * μ ^ 3) * (probability β η n * numberLogEnergy n ^ 2) +
          (5 * μ ^ 4) * (probability β η n * numberLogEnergy n) +
          (-μ ^ 5) * probability β η n) := by
      apply tsum_congr
      intro n
      unfold centeredLogEnergy internalEnergy
      dsimp [μ]
      ring
    _ = (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 5) +
        (-5 * μ) * (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 4) +
        (10 * μ ^ 2) * (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 3) +
        (-10 * μ ^ 3) * (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 2) +
        (5 * μ ^ 4) * (∑' n : ℕ, probability β η n * numberLogEnergy n) +
        (-μ ^ 5) * (∑' n : ℕ, probability β η n) := by
      rw [((((h5.add h4c).add h3c).add h2c).add h1c).tsum_add h0c,
        (((h5.add h4c).add h3c).add h2c).tsum_add h1c,
        ((h5.add h4c).add h3c).tsum_add h2c,
        (h5.add h4c).tsum_add h3c, h5.tsum_add h4c]
      simp only [tsum_mul_left]
    _ = M5 β η / Z β η
        + (-5 * μ) * (M4 β η / Z β η)
        + (10 * μ ^ 2) * (M3 β η / Z β η)
        + (-10 * μ ^ 3) * (M2 β η / Z β η)
        + (5 * μ ^ 4) * (M1 β η / Z β η)
        + (-μ ^ 5) := by
      rw [probability_fifthMoment, probability_fourthMoment,
        probability_thirdMoment, probability_secondMoment,
        probability_firstMoment, probability_tsum_eq_one β hη]
      ring
    _ = centralMoment5 β η := by
      unfold centralMoment5
      dsimp [μ]
      ring

/-- The algebraic sixth centered moment is the honest normalized countable
expectation of `(L-⟨L⟩)^6`. -/
theorem probability_centered_sixthMoment
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 6) =
      centralMoment6 β η := by
  let μ : ℝ := M1 β η / Z β η
  have h6 := summable_probability_six β hη
  have h5 := summable_probability_five β hη
  have h4 := summable_probability_four β hη
  have h3 := summable_probability_three β hη
  have h2 := summable_probability_two β hη
  have h1 := summable_probability_one β hη
  have h0 := summable_probability β hη
  have h5c := h5.mul_left (-6 * μ)
  have h4c := h4.mul_left (15 * μ ^ 2)
  have h3c := h3.mul_left (-20 * μ ^ 3)
  have h2c := h2.mul_left (15 * μ ^ 4)
  have h1c := h1.mul_left (-6 * μ ^ 5)
  have h0c := h0.mul_left (μ ^ 6)
  calc
    (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 6) =
        ∑' n : ℕ,
          (probability β η n * numberLogEnergy n ^ 6 +
          (-6 * μ) * (probability β η n * numberLogEnergy n ^ 5) +
          (15 * μ ^ 2) * (probability β η n * numberLogEnergy n ^ 4) +
          (-20 * μ ^ 3) * (probability β η n * numberLogEnergy n ^ 3) +
          (15 * μ ^ 4) * (probability β η n * numberLogEnergy n ^ 2) +
          (-6 * μ ^ 5) * (probability β η n * numberLogEnergy n) +
          (μ ^ 6) * probability β η n) := by
      apply tsum_congr
      intro n
      unfold centeredLogEnergy internalEnergy
      dsimp [μ]
      ring
    _ = (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 6) +
        (-6 * μ) * (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 5) +
        (15 * μ ^ 2) * (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 4) +
        (-20 * μ ^ 3) * (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 3) +
        (15 * μ ^ 4) * (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 2) +
        (-6 * μ ^ 5) * (∑' n : ℕ, probability β η n * numberLogEnergy n) +
        (μ ^ 6) * (∑' n : ℕ, probability β η n) := by
      rw [(((((h6.add h5c).add h4c).add h3c).add h2c).add h1c).tsum_add h0c,
        ((((h6.add h5c).add h4c).add h3c).add h2c).tsum_add h1c,
        (((h6.add h5c).add h4c).add h3c).tsum_add h2c,
        ((h6.add h5c).add h4c).tsum_add h3c,
        (h6.add h5c).tsum_add h4c, h6.tsum_add h5c]
      simp only [tsum_mul_left]
    _ = M6 β η / Z β η
        + (-6 * μ) * (M5 β η / Z β η)
        + (15 * μ ^ 2) * (M4 β η / Z β η)
        + (-20 * μ ^ 3) * (M3 β η / Z β η)
        + (15 * μ ^ 4) * (M2 β η / Z β η)
        + (-6 * μ ^ 5) * (M1 β η / Z β η)
        + μ ^ 6 := by
      rw [probability_sixthMoment, probability_fifthMoment,
        probability_fourthMoment, probability_thirdMoment,
        probability_secondMoment, probability_firstMoment,
        probability_tsum_eq_one β hη]
      ring
    _ = centralMoment6 β η := by
      unfold centralMoment6
      dsimp [μ]
      ring

end GppNumberGibbsQuadraticCenteredMoments

#print axioms GppNumberGibbsQuadraticCenteredMoments.probability_centered_fourthMoment
#print axioms GppNumberGibbsQuadraticCenteredMoments.probability_centered_fifthMoment
#print axioms GppNumberGibbsQuadraticCenteredMoments.probability_centered_sixthMoment
