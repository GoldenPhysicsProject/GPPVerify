import GppVerify.RiemannHypothesis.NumberGibbsQuadraticCenteredHigherMoments
import Mathlib.Tactic

/-!
# Quadratic number-gas curvature closure

This file closes the semantic bridge from the actual countable quadratically
confined Gibbs distribution to the centered cubic-residual algebra.  The key
identity realizes the symbolic residual square moment as the honest normalized
Gibbs expectation of a pointwise square.  Positivity of that expectation,
together with strict positivity of the centered metric determinant, yields the
scalar-curvature ceiling `R ≤ 1/2`.
-/

namespace GppNumberGibbsQuadraticCurvatureClosure

open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticNormalizedMoments
open GppNumberGibbsQuadraticCurvatureAlgebra
open GppNumberGibbsQuadraticCurvatureSquareBridge
open GppNumberGibbsQuadraticCenteredMoments

private theorem summable_probability_centered_one
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ =>
      probability β η n * centeredLogEnergy β η n) := by
  let μ : ℝ := M1 β η / Z β η
  have h1 := summable_probability_one β hη
  have h0c := (summable_probability β hη).mul_left (-μ)
  refine (h1.add h0c).congr ?_
  intro n
  unfold centeredLogEnergy internalEnergy
  dsimp [μ]
  ring

private theorem summable_probability_centered_two
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ =>
      probability β η n * centeredLogEnergy β η n ^ 2) := by
  let μ : ℝ := M1 β η / Z β η
  have h2 := summable_probability_two β hη
  have h1c := (summable_probability_one β hη).mul_left (-2 * μ)
  have h0c := (summable_probability β hη).mul_left (μ ^ 2)
  refine ((h2.add h1c).add h0c).congr ?_
  intro n
  unfold centeredLogEnergy internalEnergy
  dsimp [μ]
  ring

private theorem summable_probability_centered_three
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ =>
      probability β η n * centeredLogEnergy β η n ^ 3) := by
  let μ : ℝ := M1 β η / Z β η
  have h3 := summable_probability_three β hη
  have h2c := (summable_probability_two β hη).mul_left (-3 * μ)
  have h1c := (summable_probability_one β hη).mul_left (3 * μ ^ 2)
  have h0c := (summable_probability β hη).mul_left (-μ ^ 3)
  refine (((h3.add h2c).add h1c).add h0c).congr ?_
  intro n
  unfold centeredLogEnergy internalEnergy
  dsimp [μ]
  ring

private theorem summable_probability_centered_four
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ =>
      probability β η n * centeredLogEnergy β η n ^ 4) := by
  let μ : ℝ := M1 β η / Z β η
  have h4 := summable_probability_four β hη
  have h3c := (summable_probability_three β hη).mul_left (-4 * μ)
  have h2c := (summable_probability_two β hη).mul_left (6 * μ ^ 2)
  have h1c := (summable_probability_one β hη).mul_left (-4 * μ ^ 3)
  have h0c := (summable_probability β hη).mul_left (μ ^ 4)
  refine ((((h4.add h3c).add h2c).add h1c).add h0c).congr ?_
  intro n
  unfold centeredLogEnergy internalEnergy
  dsimp [μ]
  ring

private theorem summable_probability_centered_five
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ =>
      probability β η n * centeredLogEnergy β η n ^ 5) := by
  let μ : ℝ := M1 β η / Z β η
  have h5 := summable_probability_five β hη
  have h4c := (summable_probability_four β hη).mul_left (-5 * μ)
  have h3c := (summable_probability_three β hη).mul_left (10 * μ ^ 2)
  have h2c := (summable_probability_two β hη).mul_left (-10 * μ ^ 3)
  have h1c := (summable_probability_one β hη).mul_left (5 * μ ^ 4)
  have h0c := (summable_probability β hη).mul_left (-μ ^ 5)
  refine (((((h5.add h4c).add h3c).add h2c).add h1c).add h0c).congr ?_
  intro n
  unfold centeredLogEnergy internalEnergy
  dsimp [μ]
  ring

private theorem summable_probability_centered_six
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ =>
      probability β η n * centeredLogEnergy β η n ^ 6) := by
  let μ : ℝ := M1 β η / Z β η
  have h6 := summable_probability_six β hη
  have h5c := (summable_probability_five β hη).mul_left (-6 * μ)
  have h4c := (summable_probability_four β hη).mul_left (15 * μ ^ 2)
  have h3c := (summable_probability_three β hη).mul_left (-20 * μ ^ 3)
  have h2c := (summable_probability_two β hη).mul_left (15 * μ ^ 4)
  have h1c := (summable_probability_one β hη).mul_left (-6 * μ ^ 5)
  have h0c := (summable_probability β hη).mul_left (μ ^ 6)
  refine ((((((h6.add h5c).add h4c).add h3c).add h2c).add h1c).add h0c).congr ?_
  intro n
  unfold centeredLogEnergy internalEnergy
  dsimp [μ]
  ring

/-- The symbolic cubic-residual square moment is exactly the honest normalized
countable Gibbs expectation of the corresponding pointwise square. -/
theorem probability_cubicResidualSquare_eq_residualSqMoment
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    (∑' n : ℕ,
      probability β η n *
        (cubicResidualValue β η
          (centralMoment2 β η) (centralMoment3 β η)
          (centralMoment4 β η) (centralMoment5 β η) n) ^ 2) =
      residualSqMoment
        (centralMoment2 β η) (centralMoment3 β η)
        (centralMoment4 β η) (centralMoment5 β η)
        (centralMoment6 β η) := by
  let m2 : ℝ := centralMoment2 β η
  let m3 : ℝ := centralMoment3 β η
  let m4 : ℝ := centralMoment4 β η
  let m5 : ℝ := centralMoment5 β η
  let m6 : ℝ := centralMoment6 β η
  let D : ℝ := metricDet m2 m3 m4
  let A : ℝ := residualC0 m2 m3 m4 m5
  let B : ℝ := residualC1 m2 m3 m4 m5
  let C : ℝ := residualC2 m2 m3 m4 m5
  change
    (∑' n : ℕ,
      probability β η n *
        (cubicResidualValue β η m2 m3 m4 m5 n) ^ 2) =
      residualSqMoment m2 m3 m4 m5 m6
  have h0 := summable_probability β hη
  have h1 := summable_probability_centered_one β hη
  have h2 := summable_probability_centered_two β hη
  have h3 := summable_probability_centered_three β hη
  have h4 := summable_probability_centered_four β hη
  have h5 := summable_probability_centered_five β hη
  have h6 := summable_probability_centered_six β hη
  have h0c := h0.mul_left (A ^ 2)
  have h1c := h1.mul_left (2 * A * B)
  have h2c := h2.mul_left (B ^ 2 + 2 * A * C)
  have h3c := h3.mul_left (2 * A * D + 2 * B * C)
  have h4c := h4.mul_left (C ^ 2 + 2 * B * D)
  have h5c := h5.mul_left (2 * C * D)
  have h6c := h6.mul_left (D ^ 2)
  calc
    (∑' n : ℕ,
      probability β η n *
        (cubicResidualValue β η m2 m3 m4 m5 n) ^ 2) =
      ∑' n : ℕ,
        ((A ^ 2) * probability β η n
          + (2 * A * B) *
              (probability β η n * centeredLogEnergy β η n)
          + (B ^ 2 + 2 * A * C) *
              (probability β η n * centeredLogEnergy β η n ^ 2)
          + (2 * A * D + 2 * B * C) *
              (probability β η n * centeredLogEnergy β η n ^ 3)
          + (C ^ 2 + 2 * B * D) *
              (probability β η n * centeredLogEnergy β η n ^ 4)
          + (2 * C * D) *
              (probability β η n * centeredLogEnergy β η n ^ 5)
          + (D ^ 2) *
              (probability β η n * centeredLogEnergy β η n ^ 6)) := by
        apply tsum_congr
        intro n
        unfold cubicResidualValue
        dsimp [D, A, B, C]
        ring
    _ = (A ^ 2) * (∑' n : ℕ, probability β η n)
          + (2 * A * B) *
              (∑' n : ℕ, probability β η n * centeredLogEnergy β η n)
          + (B ^ 2 + 2 * A * C) *
              (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 2)
          + (2 * A * D + 2 * B * C) *
              (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 3)
          + (C ^ 2 + 2 * B * D) *
              (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 4)
          + (2 * C * D) *
              (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 5)
          + (D ^ 2) *
              (∑' n : ℕ, probability β η n * centeredLogEnergy β η n ^ 6) := by
        rw [(((((h0c.add h1c).add h2c).add h3c).add h4c).add h5c).tsum_add h6c,
          ((((h0c.add h1c).add h2c).add h3c).add h4c).tsum_add h5c,
          (((h0c.add h1c).add h2c).add h3c).tsum_add h4c,
          ((h0c.add h1c).add h2c).tsum_add h3c,
          (h0c.add h1c).tsum_add h2c, h0c.tsum_add h1c]
        simp only [tsum_mul_left]
    _ = A ^ 2
          + (2 * A * B) * 0
          + (B ^ 2 + 2 * A * C) * m2
          + (2 * A * D + 2 * B * C) * m3
          + (C ^ 2 + 2 * B * D) * m4
          + (2 * C * D) * m5
          + (D ^ 2) * m6 := by
        rw [probability_tsum_eq_one β hη,
          probability_centered_firstMoment_eq_zero β hη,
          probability_centered_secondMoment β hη,
          probability_centered_thirdMoment β hη,
          probability_centered_fourthMoment β hη,
          probability_centered_fifthMoment β hη,
          probability_centered_sixthMoment β hη]
        simp [m2, m3, m4, m5, m6]
    _ = residualSqMoment m2 m3 m4 m5 m6 := by
        exact cubicResidual_centeredMoment_expansion m2 m3 m4 m5 m6

/-- The actual two-parameter quadratically confined number Gibbs metric has
scalar curvature at most one half throughout the domain `η > 0`. -/
theorem numberGibbs_scalarCurvature_le_half
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    scalarCurvature
      (centralMoment2 β η) (centralMoment3 β η)
      (centralMoment4 β η) (centralMoment5 β η)
      (centralMoment6 β η) ≤ (1 : ℝ) / 2 := by
  have hprob : ∀ n : ℕ, 0 ≤ probability β η n := by
    intro n
    unfold probability
    exact div_nonneg (numberGibbsWeight_nonneg β η n) (Z_pos β hη).le
  have hsquare :
      0 ≤ (∑' n : ℕ,
        probability β η n *
          (cubicResidualValue β η
            (centralMoment2 β η) (centralMoment3 β η)
            (centralMoment4 β η) (centralMoment5 β η) n) ^ 2) :=
    tsum_nonneg (fun n =>
      mul_nonneg (hprob n)
        (sq_nonneg (cubicResidualValue β η
          (centralMoment2 β η) (centralMoment3 β η)
          (centralMoment4 β η) (centralMoment5 β η) n)))
  have hres :
      0 ≤ residualSqMoment
        (centralMoment2 β η) (centralMoment3 β η)
        (centralMoment4 β η) (centralMoment5 β η)
        (centralMoment6 β η) := by
    rw [← probability_cubicResidualSquare_eq_residualSqMoment β hη]
    exact hsquare
  exact scalarCurvature_le_half_of_residualSqMoment_nonneg
    (centralMoment2 β η) (centralMoment3 β η)
    (centralMoment4 β η) (centralMoment5 β η)
    (centralMoment6 β η)
    (central_metricDet_pos β hη) hres

end GppNumberGibbsQuadraticCurvatureClosure

#print axioms GppNumberGibbsQuadraticCurvatureClosure.probability_cubicResidualSquare_eq_residualSqMoment
#print axioms GppNumberGibbsQuadraticCurvatureClosure.numberGibbs_scalarCurvature_le_half
