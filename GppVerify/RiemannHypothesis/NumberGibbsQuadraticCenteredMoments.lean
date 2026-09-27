import GppVerify.RiemannHypothesis.NumberGibbsQuadraticNormalizedMoments
import GppVerify.RiemannHypothesis.NumberGibbsQuadraticCurvatureSquareBridge
import GppVerify.RiemannHypothesis.NumberGibbsQuadraticMassieuFisherIdentification
import Mathlib.Tactic

/-!
# Centered moments for the quadratically confined number Gibbs family

This file begins the final semantic curvature bridge. It packages the actual
centered moments in terms of the normalized raw moments, proves that the
centered metric determinant is exactly the already-certified normalized Fisher
determinant, and identifies the first two centered moments with honest
countable Gibbs `tsum`s.
-/

namespace GppNumberGibbsQuadraticCenteredMoments

open GppFiniteFisherMomentBridge
open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticNormalizedMoments
open GppNumberGibbsQuadraticCurvatureSquareBridge
open GppNumberGibbsQuadraticCurvatureAlgebra
open GppNumberGibbsQuadraticMassieuFisherIdentification

noncomputable def centralMoment2 (β η : ℝ) : ℝ :=
  M2 β η / Z β η - (M1 β η / Z β η) ^ 2

noncomputable def centralMoment3 (β η : ℝ) : ℝ :=
  M3 β η / Z β η
    - 3 * (M1 β η / Z β η) * (M2 β η / Z β η)
    + 2 * (M1 β η / Z β η) ^ 3

noncomputable def centralMoment4 (β η : ℝ) : ℝ :=
  M4 β η / Z β η
    - 4 * (M1 β η / Z β η) * (M3 β η / Z β η)
    + 6 * (M1 β η / Z β η) ^ 2 * (M2 β η / Z β η)
    - 3 * (M1 β η / Z β η) ^ 4

noncomputable def centralMoment5 (β η : ℝ) : ℝ :=
  M5 β η / Z β η
    - 5 * (M1 β η / Z β η) * (M4 β η / Z β η)
    + 10 * (M1 β η / Z β η) ^ 2 * (M3 β η / Z β η)
    - 10 * (M1 β η / Z β η) ^ 3 * (M2 β η / Z β η)
    + 4 * (M1 β η / Z β η) ^ 5

noncomputable def centralMoment6 (β η : ℝ) : ℝ :=
  M6 β η / Z β η
    - 6 * (M1 β η / Z β η) * (M5 β η / Z β η)
    + 15 * (M1 β η / Z β η) ^ 2 * (M4 β η / Z β η)
    - 20 * (M1 β η / Z β η) ^ 3 * (M3 β η / Z β η)
    + 15 * (M1 β η / Z β η) ^ 4 * (M2 β η / Z β η)
    - 5 * (M1 β η / Z β η) ^ 6

/-- Translation from the raw covariance determinant of `L,L^2` to the
centered determinant used by the curvature algebra. -/
theorem fisherDet_eq_metricDet_central (β η : ℝ) :
    fisherDet (M1 β η / Z β η) (M2 β η / Z β η)
        (M3 β η / Z β η) (M4 β η / Z β η) =
      metricDet (centralMoment2 β η) (centralMoment3 β η)
        (centralMoment4 β η) := by
  unfold fisherDet metricDet centralMoment2 centralMoment3 centralMoment4
  ring

/-- The actual centered metric determinant is strictly positive throughout the
quadratically confined domain. -/
theorem central_metricDet_pos
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    0 < metricDet (centralMoment2 β η) (centralMoment3 β η)
      (centralMoment4 β η) := by
  have h := massieuFisherDet_pos β hη
  rw [massieuFisherDet_eq_normalized_fisherDet] at h
  rw [fisherDet_eq_metricDet_central] at h
  exact h

/-- The mean of the actual centered log-energy observable is zero. -/
theorem probability_centered_firstMoment_eq_zero
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    (∑' n : ℕ, probability β η n * centeredLogEnergy β η n) = 0 := by
  let μ : ℝ := M1 β η / Z β η
  have h1 := summable_probability_one β hη
  have h0 := summable_probability β hη
  have h0c := h0.mul_left (-μ)
  calc
    (∑' n : ℕ, probability β η n * centeredLogEnergy β η n) =
        ∑' n : ℕ,
          (probability β η n * numberLogEnergy n +
            (-μ) * probability β η n) := by
      apply tsum_congr
      intro n
      unfold centeredLogEnergy internalEnergy
      dsimp [μ]
      ring
    _ = (∑' n : ℕ, probability β η n * numberLogEnergy n) +
        (-μ) * (∑' n : ℕ, probability β η n) := by
      rw [h1.tsum_add h0c]
      simp only [tsum_mul_left]
    _ = M1 β η / Z β η + (-μ) * 1 := by
      rw [probability_firstMoment, probability_tsum_eq_one β hη]
    _ = 0 := by
      dsimp [μ]
      ring

/-- The algebraic second centered moment is the honest normalized countable
expectation of `(L-⟨L⟩)^2`. -/
theorem probability_centered_secondMoment
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 2) =
      centralMoment2 β η := by
  let μ : ℝ := M1 β η / Z β η
  have h2 := summable_probability_two β hη
  have h1 := summable_probability_one β hη
  have h0 := summable_probability β hη
  have h1c := h1.mul_left (-2 * μ)
  have h0c := h0.mul_left (μ ^ 2)
  calc
    (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 2) =
        ∑' n : ℕ,
          (probability β η n * numberLogEnergy n ^ 2 +
          (-2 * μ) * (probability β η n * numberLogEnergy n) +
          (μ ^ 2) * probability β η n) := by
      apply tsum_congr
      intro n
      unfold centeredLogEnergy internalEnergy
      dsimp [μ]
      ring
    _ = (∑' n : ℕ, probability β η n * numberLogEnergy n ^ 2) +
        (-2 * μ) * (∑' n : ℕ, probability β η n * numberLogEnergy n) +
        (μ ^ 2) * (∑' n : ℕ, probability β η n) := by
      rw [(h2.add h1c).tsum_add h0c, h2.tsum_add h1c]
      simp only [tsum_mul_left]
    _ = M2 β η / Z β η + (-2 * μ) * (M1 β η / Z β η) + μ ^ 2 := by
      rw [probability_secondMoment, probability_firstMoment,
        probability_tsum_eq_one β hη]
      ring
    _ = centralMoment2 β η := by
      unfold centralMoment2
      dsimp [μ]
      ring

end GppNumberGibbsQuadraticCenteredMoments

#print axioms GppNumberGibbsQuadraticCenteredMoments.fisherDet_eq_metricDet_central
#print axioms GppNumberGibbsQuadraticCenteredMoments.central_metricDet_pos
#print axioms GppNumberGibbsQuadraticCenteredMoments.probability_centered_firstMoment_eq_zero
#print axioms GppNumberGibbsQuadraticCenteredMoments.probability_centered_secondMoment
