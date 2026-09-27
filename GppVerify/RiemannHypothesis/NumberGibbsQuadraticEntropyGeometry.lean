import GppVerify.RiemannHypothesis.NumberGibbsQuadraticMassieuMetric
import Mathlib.Tactic

/-!
# Entropy gradient and Fisher geometry for the quadratically confined number Gibbs gas

For

  S(β,η) = log Z + β⟨L⟩ + η⟨L²⟩,

the exact Massieu and moment derivative laws imply

  ∂β S = -(β gββ + η gβη),
  ∂η S = -(β gβη + η gηη).

Thus the entropy gradient is the negative Fisher/covariance matrix applied to the
natural-parameter vector.  Contracting with `(β,η)` gives the radial entropy-response
quadratic form.  Since the confined Fisher matrix is already strictly positive definite,
the radial entropy response is strictly negative throughout `η>0`.
-/

namespace GppNumberGibbsQuadraticEntropyGeometry

open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticMassieuDerivatives
open GppNumberGibbsQuadraticMassieuHessian
open GppNumberGibbsQuadraticMassieuMetric

/-- The `β` entropy derivative is minus the first component of the Fisher matrix
applied to the natural-parameter vector `(β,η)`. -/
theorem hasDerivAt_entropy_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt
      (fun b : ℝ => entropy b η)
      (-(β * fisherBB β η + η * fisherBE β η)) β := by
  have hlog := hasDerivAt_logZ_beta β hη
  have hU := hasDerivAt_internalEnergy_beta β hη
  have hQ := hasDerivAt_quadraticEnergy_beta β hη
  have hβU := (hasDerivAt_id β).mul hU
  have hηQ := (hasDerivAt_const (x := β) η).mul hQ
  have H := (hlog.add hβU).add hηQ
  convert H using 1 <;> simp [entropy] <;> ring

/-- The `η` entropy derivative is minus the second component of the Fisher matrix
applied to the natural-parameter vector `(β,η)`. -/
theorem hasDerivAt_entropy_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt
      (fun e : ℝ => entropy β e)
      (-(β * fisherBE β η + η * fisherEE β η)) η := by
  have hlog := hasDerivAt_logZ_eta β hη
  have hU := hasDerivAt_internalEnergy_eta β hη
  have hQ := hasDerivAt_quadraticEnergy_eta β hη
  have hβU := (hasDerivAt_const (x := η) β).mul hU
  have hηQ := (hasDerivAt_id η).mul hQ
  have H := (hlog.add hβU).add hηQ
  convert H using 1 <;> simp [entropy] <;> ring

/-- Algebraic radial contraction of the entropy-gradient components. -/
theorem radial_entropy_gradient_eq_neg_fisher_quadratic
    (β η : ℝ) :
    β * (-(β * fisherBB β η + η * fisherBE β η)) +
        η * (-(β * fisherBE β η + η * fisherEE β η)) =
      -(β ^ 2 * fisherBB β η +
        2 * β * η * fisherBE β η +
        η ^ 2 * fisherEE β η) := by
  ring

/-- On the genuinely confined domain, the radial entropy response in natural-parameter
space is strictly negative.  This is the differential form of entropy loss along a
positive scaling of `(β,η)`, and is exactly minus the Fisher fluctuation norm. -/
theorem radial_entropy_gradient_neg
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    β * (-(β * fisherBB β η + η * fisherBE β η)) +
        η * (-(β * fisherBE β η + η * fisherEE β η)) < 0 := by
  have hq :
      0 < fisherBB β η * β ^ 2 +
          2 * fisherBE β η * β * η +
          fisherEE β η * η ^ 2 := by
    exact massieuFisher_quadratic_form_pos β hη β η (Or.inr (ne_of_gt hη))
  rw [radial_entropy_gradient_eq_neg_fisher_quadratic]
  have hq' :
      0 < β ^ 2 * fisherBB β η +
          2 * β * η * fisherBE β η +
          η ^ 2 * fisherEE β η := by
    nlinarith
  exact neg_lt_zero.mpr hq'

/-- The confined number-Gibbs entropy has no stationary point in natural-parameter
space: its two coordinate derivative values cannot vanish simultaneously when `η>0`.
This follows without any curvature sign assumption, solely from strict Fisher
positive-definiteness and the radial entropy identity. -/
theorem entropy_gradient_values_not_both_zero
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    ¬ ((-(β * fisherBB β η + η * fisherBE β η) = 0) ∧
       (-(β * fisherBE β η + η * fisherEE β η) = 0)) := by
  intro hzero
  have hneg := radial_entropy_gradient_neg β hη
  rw [hzero.1, hzero.2] at hneg
  norm_num at hneg

end GppNumberGibbsQuadraticEntropyGeometry

#print axioms GppNumberGibbsQuadraticEntropyGeometry.hasDerivAt_entropy_beta
#print axioms GppNumberGibbsQuadraticEntropyGeometry.hasDerivAt_entropy_eta
#print axioms GppNumberGibbsQuadraticEntropyGeometry.radial_entropy_gradient_eq_neg_fisher_quadratic
#print axioms GppNumberGibbsQuadraticEntropyGeometry.radial_entropy_gradient_neg
#print axioms GppNumberGibbsQuadraticEntropyGeometry.entropy_gradient_values_not_both_zero
