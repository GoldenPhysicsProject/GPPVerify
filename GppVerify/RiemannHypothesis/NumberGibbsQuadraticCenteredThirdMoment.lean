import GppVerify.RiemannHypothesis.NumberGibbsQuadraticCenteredMoments
import Mathlib.Tactic

/-!
# Third centered moment for the quadratically confined number Gibbs family

This file continues the final semantic curvature bridge by identifying the
algebraic third centered moment with the honest normalized countable Gibbs
expectation of the cubic centered log-energy observable.
-/

namespace GppNumberGibbsQuadraticCenteredMoments

open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticNormalizedMoments
open GppNumberGibbsQuadraticCurvatureSquareBridge

/-- The algebraic third centered moment is the honest normalized countable
expectation of `(L-⟨L⟩)^3`. -/
theorem probability_centered_thirdMoment
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 3) =
      centralMoment3 β η := by
  let μ : ℝ := M1 β η / Z β η
  have h3 := summable_probability_three β hη
  have h2 := summable_probability_two β hη
  have h1 := summable_probability_one β hη
  have h0 := summable_probability β hη
  have h2c := h2.mul_left (-3 * μ)
  have h1c := h1.mul_left (3 * μ ^ 2)
  have h0c := h0.mul_left (-μ ^ 3)
  calc
    (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 3) =
        ∑' n : ℕ,
          (probability β η n * numberLogEnergy n ^ 3 +
          (-3 * μ) * (probability β η n * numberLogEnergy n ^ 2) +
          (3 * μ ^ 2) * (probability β η n * numberLogEnergy n) +
          (-μ ^ 3) * probability β η n) := by
      apply tsum_congr
      intro n
      unfold centeredLogEnergy internalEnergy
      dsimp [μ]
      ring
    _ = (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 3) +
        (-3 * μ) * (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 2) +
        (3 * μ ^ 2) * (∑' n : ℕ, probability β η n * numberLogEnergy n) +
        (-μ ^ 3) * (∑' n : ℕ, probability β η n) := by
      rw [((h3.add h2c).add h1c).tsum_add h0c,
        (h3.add h2c).tsum_add h1c, h3.tsum_add h2c]
      simp only [tsum_mul_left]
    _ = M3 β η / Z β η
        + (-3 * μ) * (M2 β η / Z β η)
        + (3 * μ ^ 2) * (M1 β η / Z β η)
        + (-μ ^ 3) := by
      rw [probability_thirdMoment, probability_secondMoment,
        probability_firstMoment, probability_tsum_eq_one β hη]
      ring
    _ = centralMoment3 β η := by
      unfold centralMoment3
      dsimp [μ]
      ring

end GppNumberGibbsQuadraticCenteredMoments

#print axioms GppNumberGibbsQuadraticCenteredMoments.probability_centered_thirdMoment
