import GppVerify.RiemannHypothesis.NumberGibbsQuadraticCurvatureClosure
import GppVerify.RiemannHypothesis.NumberGibbsQuadraticCurvatureStrictAlgebra
import GppVerify.RiemannHypothesis.PrimeHankelInfiniteLift
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree

/-!
# Strict quadratic number-gas curvature closure

This module upgrades the certified bound `R ≤ 1/2` to the strict bound `R < 1/2`.
The semantic input is elementary but genuinely countable: the denominator-cleared
residual is a nonzero cubic because its leading coefficient is the strictly positive
metric determinant, while the centered logarithmic support contains four distinct
points of strictly positive Gibbs weight.  The existing polynomial root-escape and
finite-to-infinite lifting theorem therefore makes the cubic-square Gibbs expectation
strictly positive.
-/

namespace GppNumberGibbsQuadraticCurvatureStrictClosure

open Polynomial BigOperators
open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticNormalizedMoments
open GppNumberGibbsQuadraticCurvatureAlgebra
open GppNumberGibbsQuadraticCurvatureSquareBridge
open GppNumberGibbsQuadraticCenteredMoments
open GppNumberGibbsQuadraticCurvatureClosure
open GppNumberGibbsQuadraticCurvatureStrictAlgebra
open GppPrimeHankelInfiniteLift

/-- The logarithmic number observable is injective. -/
theorem numberLogEnergy_injective : Function.Injective numberLogEnergy := by
  intro a b hab
  unfold numberLogEnergy at hab
  have hcast : (a : ℝ) + 1 = (b : ℝ) + 1 := by
    have h := congrArg Real.exp hab
    rw [Real.exp_log (by positivity), Real.exp_log (by positivity)] at h
    exact h
  have habr : (a : ℝ) = (b : ℝ) := by linarith
  exact_mod_cast habr

/-- Subtracting the Gibbs mean preserves distinctness of the logarithmic support. -/
theorem centeredLogEnergy_injective (β η : ℝ) :
    Function.Injective (centeredLogEnergy β η) := by
  intro a b hab
  unfold centeredLogEnergy at hab
  apply numberLogEnergy_injective
  linarith

/-- Every normalized quadratic Gibbs probability is strictly positive on `η > 0`. -/
theorem probability_pos (β : ℝ) {η : ℝ} (hη : 0 < η) (n : ℕ) :
    0 < probability β η n := by
  unfold probability
  exact div_pos (numberGibbsWeight_pos β η n) (Z_pos β hη)

private theorem summable_probability_centered_one
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ => probability β η n * centeredLogEnergy β η n) := by
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
    Summable (fun n : ℕ => probability β η n * centeredLogEnergy β η n ^ 2) := by
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
    Summable (fun n : ℕ => probability β η n * centeredLogEnergy β η n ^ 3) := by
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
    Summable (fun n : ℕ => probability β η n * centeredLogEnergy β η n ^ 4) := by
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
    Summable (fun n : ℕ => probability β η n * centeredLogEnergy β η n ^ 5) := by
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
    Summable (fun n : ℕ => probability β η n * centeredLogEnergy β η n ^ 6) := by
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

/-- Polynomial whose evaluation is exactly the denominator-cleared cubic residual. -/
noncomputable def residualPolynomial (m2 m3 m4 m5 : ℝ) : ℝ[X] :=
  Polynomial.C (residualC0 m2 m3 m4 m5)
    + Polynomial.C (residualC1 m2 m3 m4 m5) * Polynomial.X
    + Polynomial.C (residualC2 m2 m3 m4 m5) * Polynomial.X ^ 2
    + Polynomial.C (metricDet m2 m3 m4) * Polynomial.X ^ 3

/-- Evaluation of `residualPolynomial` agrees with the pointwise residual. -/
theorem residualPolynomial_eval
    (β η m2 m3 m4 m5 : ℝ) (n : ℕ) :
    (residualPolynomial m2 m3 m4 m5).eval (centeredLogEnergy β η n) =
      cubicResidualValue β η m2 m3 m4 m5 n := by
  simp [residualPolynomial, cubicResidualValue]
  ring

/-- Positive metric determinant makes the residual polynomial genuinely cubic. -/
theorem residualPolynomial_ne_zero
    (m2 m3 m4 m5 : ℝ) (hD : 0 < metricDet m2 m3 m4) :
    residualPolynomial m2 m3 m4 m5 ≠ 0 := by
  intro hp
  have hc := congrArg (fun p : ℝ[X] => p.coeff 3) hp
  have hzero : metricDet m2 m3 m4 = 0 := by
    simpa [residualPolynomial] using hc
  exact hD.ne' hzero

/-- The residual polynomial has degree at most three. -/
theorem residualPolynomial_natDegree_le_three
    (m2 m3 m4 m5 : ℝ) :
    (residualPolynomial m2 m3 m4 m5).natDegree ≤ 3 := by
  unfold residualPolynomial
  compute_degree

/-- The actual normalized cubic-square integrand is summable. -/
theorem summable_probability_cubicResidualSquare
    (β : ℝ) {η : ℝ} (hη : 0 < η)
    (m2 m3 m4 m5 : ℝ) :
    Summable (fun n : ℕ =>
      probability β η n * (cubicResidualValue β η m2 m3 m4 m5 n) ^ 2) := by
  let D : ℝ := metricDet m2 m3 m4
  let A : ℝ := residualC0 m2 m3 m4 m5
  let B : ℝ := residualC1 m2 m3 m4 m5
  let C : ℝ := residualC2 m2 m3 m4 m5
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
  refine ((((((h0c.add h1c).add h2c).add h3c).add h4c).add h5c).add h6c).congr ?_
  intro n
  unfold cubicResidualValue
  dsimp [D, A, B, C]
  ring

/-- The honest cubic residual square has strictly positive Gibbs expectation. -/
theorem probability_cubicResidualSquare_pos
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    0 < ∑' n : ℕ,
      probability β η n *
        (cubicResidualValue β η
          (centralMoment2 β η) (centralMoment3 β η)
          (centralMoment4 β η) (centralMoment5 β η) n) ^ 2 := by
  let m2 : ℝ := centralMoment2 β η
  let m3 : ℝ := centralMoment3 β η
  let m4 : ℝ := centralMoment4 β η
  let m5 : ℝ := centralMoment5 β η
  let p : ℝ[X] := residualPolynomial m2 m3 m4 m5
  let x : ℕ → ℝ := centeredLogEnergy β η
  let w : ℕ → ℝ := probability β η
  let S : Finset ℕ := Finset.range 4
  have hD : 0 < metricDet m2 m3 m4 := by
    dsimp [m2, m3, m4]
    exact central_metricDet_pos β hη
  have hp : p ≠ 0 := by
    dsimp [p]
    exact residualPolynomial_ne_zero m2 m3 m4 m5 hD
  have hdeg : p.natDegree ≤ 3 := by
    dsimp [p]
    exact residualPolynomial_natDegree_le_three m2 m3 m4 m5
  have hcard : 3 < (S.image x).card := by
    have hinj : Function.Injective x := by
      dsimp [x]
      exact centeredLogEnergy_injective β η
    rw [Finset.card_image_iff.mpr hinj.injOn]
    simp [S]
  have hw : ∀ n : ℕ, 0 ≤ w n := by
    intro n
    exact (probability_pos β hη n).le
  have hwS : ∀ n ∈ S, 0 < w n := by
    intro n hn
    exact probability_pos β hη n
  have hsum : Summable (fun n : ℕ => w n * (p.eval (x n)) ^ 2) := by
    have h := summable_probability_cubicResidualSquare β hη m2 m3 m4 m5
    refine h.congr ?_
    intro n
    dsimp [w, p, x]
    rw [residualPolynomial_eval]
  have hpos := weighted_polynomial_tsum_pos p x w S 3 hp hdeg hcard hw hwS hsum
  simpa [p, x, w, m2, m3, m4, m5, residualPolynomial_eval] using hpos

/-- **Strict quadratic number-gas curvature theorem.**  For every real `β` and
strictly positive quadratic-confinement parameter `η`, the scalar curvature of
the genuine two-parameter number-Gibbs Fisher metric is strictly below one half. -/
theorem numberGibbs_scalarCurvature_lt_half
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    scalarCurvature
      (centralMoment2 β η) (centralMoment3 β η)
      (centralMoment4 β η) (centralMoment5 β η)
      (centralMoment6 β η) < (1 : ℝ) / 2 := by
  have hres :
      0 < residualSqMoment
        (centralMoment2 β η) (centralMoment3 β η)
        (centralMoment4 β η) (centralMoment5 β η)
        (centralMoment6 β η) := by
    rw [← probability_cubicResidualSquare_eq_residualSqMoment β hη]
    exact probability_cubicResidualSquare_pos β hη
  exact scalarCurvature_lt_half_of_residualSqMoment_pos
    (centralMoment2 β η) (centralMoment3 β η)
    (centralMoment4 β η) (centralMoment5 β η)
    (centralMoment6 β η)
    (central_metricDet_pos β hη) hres

end GppNumberGibbsQuadraticCurvatureStrictClosure

#print axioms GppNumberGibbsQuadraticCurvatureStrictClosure.numberLogEnergy_injective
#print axioms GppNumberGibbsQuadraticCurvatureStrictClosure.residualPolynomial_ne_zero
#print axioms GppNumberGibbsQuadraticCurvatureStrictClosure.probability_cubicResidualSquare_pos
#print axioms GppNumberGibbsQuadraticCurvatureStrictClosure.numberGibbs_scalarCurvature_lt_half
