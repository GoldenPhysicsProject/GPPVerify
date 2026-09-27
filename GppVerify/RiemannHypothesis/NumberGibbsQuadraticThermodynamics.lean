import GppVerify.RiemannHypothesis.NumberGibbsQuadraticCurvatureSummability
import Mathlib.Tactic

/-!
# Thermodynamics of the quadratically confined number-Gibbs family

For arbitrary real `β` and strictly positive `η`, quadratic log-confinement makes the
partition function and the first six log-energy moments absolutely summable.  This file
packages the corresponding normalized observables and the exact two-parameter Gibbs
entropy/Legendre identities.  No differentiability of the partition function is used here.
-/

namespace GppNumberGibbsQuadraticThermodynamics

open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticConfinement
open GppNumberGibbsQuadraticCurvatureSummability
open GppZetaGibbsSummability

/-- Quadratically confined partition function. -/
noncomputable def Z (β η : ℝ) : ℝ :=
  ∑' n : ℕ, numberGibbsWeight β η n

/-- First raw log-energy moment. -/
noncomputable def M1 (β η : ℝ) : ℝ :=
  ∑' n : ℕ, numberGibbsWeight β η n * numberLogEnergy n

/-- Second raw log-energy moment. -/
noncomputable def M2 (β η : ℝ) : ℝ :=
  ∑' n : ℕ, numberGibbsWeight β η n * numberLogEnergy n ^ 2

/-- Third raw log-energy moment. -/
noncomputable def M3 (β η : ℝ) : ℝ :=
  ∑' n : ℕ, numberGibbsWeight β η n * numberLogEnergy n ^ 3

/-- Fourth raw log-energy moment. -/
noncomputable def M4 (β η : ℝ) : ℝ :=
  ∑' n : ℕ, numberGibbsWeight β η n * numberLogEnergy n ^ 4

/-- Fifth raw log-energy moment. -/
noncomputable def M5 (β η : ℝ) : ℝ :=
  ∑' n : ℕ, numberGibbsWeight β η n * numberLogEnergy n ^ 5

/-- Sixth raw log-energy moment. -/
noncomputable def M6 (β η : ℝ) : ℝ :=
  ∑' n : ℕ, numberGibbsWeight β η n * numberLogEnergy n ^ 6

/-- Mean log-energy. -/
noncomputable def internalEnergy (β η : ℝ) : ℝ := M1 β η / Z β η

/-- Mean squared log-energy, conjugate to the quadratic confinement parameter. -/
noncomputable def quadraticEnergy (β η : ℝ) : ℝ := M2 β η / Z β η

/-- Two-parameter Gibbs entropy `log Z + β⟨L⟩ + η⟨L²⟩`. -/
noncomputable def entropy (β η : ℝ) : ℝ :=
  Real.log (Z β η) + β * internalEnergy β η + η * quadraticEnergy β η

/-- Helmholtz coordinate with respect to `β` at fixed `η`. -/
noncomputable def freeEnergy (β η : ℝ) : ℝ := -(Real.log (Z β η)) / β

/-- Quadratic confinement makes the partition-weight series summable for every real `β`. -/
theorem summable_numberGibbsWeight
    (β : ℝ) {η : ℝ} (hη : 0 < η) : Summable (numberGibbsWeight β η) := by
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz0 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 0) := by
    simpa using summable_gibbsWeight htwo
  have h := summable_numberGibbs_moment_of_quadratic β η 0 hη hz0
  simpa using h

/-- The fifth raw moment integrand is absolutely summable throughout the confined domain. -/
theorem summable_M5_integrand
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ => numberGibbsWeight β η n * numberLogEnergy n ^ 5) := by
  exact summable_numberGibbs_moment_fifth_of_eta_pos β hη

/-- The sixth raw moment integrand is absolutely summable throughout the confined domain. -/
theorem summable_M6_integrand
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ => numberGibbsWeight β η n * numberLogEnergy n ^ 6) := by
  exact summable_numberGibbs_moment_sixth_of_eta_pos β hη

/-- The quadratically confined partition function is strictly positive for every real `β`. -/
theorem Z_pos (β : ℝ) {η : ℝ} (hη : 0 < η) : 0 < Z β η := by
  have hnonneg : ∀ n : ℕ, 0 ≤ numberGibbsWeight β η n := by
    intro n
    exact numberGibbsWeight_nonneg β η n
  have hzero : 0 < numberGibbsWeight β η 0 := numberGibbsWeight_pos β η 0
  unfold Z
  exact (summable_numberGibbsWeight β hη).tsum_pos hnonneg 0 hzero

/-- Exact two-parameter Massieu balance. -/
theorem entropy_sub_conjugate_terms_eq_logZ (β η : ℝ) :
    entropy β η - β * internalEnergy β η - η * quadraticEnergy β η =
      Real.log (Z β η) := by
  unfold entropy
  ring

/-- Away from `β = 0`, the free-energy coordinate satisfies `βF = -log Z`. -/
theorem beta_mul_freeEnergy_eq_neg_logZ
    {β η : ℝ} (hβ : β ≠ 0) :
    β * freeEnergy β η = -Real.log (Z β η) := by
  unfold freeEnergy
  field_simp [hβ] <;> ring

/-- Exact generalized Legendre relation at fixed quadratic coupling. -/
theorem entropy_eq_beta_mul_internalEnergy_sub_freeEnergy_add_quadratic
    {β η : ℝ} (hβ : β ≠ 0) :
    entropy β η =
      β * (internalEnergy β η - freeEnergy β η) + η * quadraticEnergy β η := by
  unfold entropy freeEnergy
  field_simp [hβ] <;> ring

/-- Equivalent generalized free-energy identity. -/
theorem freeEnergy_eq_internalEnergy_add_quadratic_div_sub_entropy_div
    {β η : ℝ} (hβ : β ≠ 0) :
    freeEnergy β η = internalEnergy β η +
      (η / β) * quadraticEnergy β η - entropy β η / β := by
  unfold entropy freeEnergy
  field_simp [hβ] <;> ring

/-- Honest thermodynamic package on the fully confined domain `η > 0`. -/
theorem quadratic_gibbs_legendre_package
    (β : ℝ) {η : ℝ} (hη : 0 < η) (hβ : β ≠ 0) :
    0 < Z β η ∧
      entropy β η =
        β * (internalEnergy β η - freeEnergy β η) + η * quadraticEnergy β η ∧
      freeEnergy β η = internalEnergy β η +
        (η / β) * quadraticEnergy β η - entropy β η / β := by
  exact ⟨Z_pos β hη,
    entropy_eq_beta_mul_internalEnergy_sub_freeEnergy_add_quadratic hβ,
    freeEnergy_eq_internalEnergy_add_quadratic_div_sub_entropy_div hβ⟩

end GppNumberGibbsQuadraticThermodynamics

#print axioms GppNumberGibbsQuadraticThermodynamics.summable_numberGibbsWeight
#print axioms GppNumberGibbsQuadraticThermodynamics.summable_M5_integrand
#print axioms GppNumberGibbsQuadraticThermodynamics.summable_M6_integrand
#print axioms GppNumberGibbsQuadraticThermodynamics.Z_pos
#print axioms GppNumberGibbsQuadraticThermodynamics.entropy_sub_conjugate_terms_eq_logZ
#print axioms GppNumberGibbsQuadraticThermodynamics.entropy_eq_beta_mul_internalEnergy_sub_freeEnergy_add_quadratic
#print axioms GppNumberGibbsQuadraticThermodynamics.freeEnergy_eq_internalEnergy_add_quadratic_div_sub_entropy_div
#print axioms GppNumberGibbsQuadraticThermodynamics.quadratic_gibbs_legendre_package
