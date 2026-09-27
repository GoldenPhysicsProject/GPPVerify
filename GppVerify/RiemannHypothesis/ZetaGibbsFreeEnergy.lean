import GppVerify.RiemannHypothesis.ZetaGibbsFisher
import Mathlib.Tactic

/-!
# Entropy and free energy of the zeta Gibbs family

For `β>1` the partition sum is an honest positive Gibbs partition function.  This file
adds the standard dimensionless internal-energy, entropy, and free-energy coordinates
and records their exact algebraic Legendre relation.  No analytic continuation of these
thermodynamic quantities is asserted.
-/

namespace GppZetaGibbsFreeEnergy

open GppZetaGibbsSummability
open GppZetaGibbsFisher

/-- Mean logarithmic energy. -/
noncomputable def internalEnergy (β : ℝ) : ℝ := M1 β / Z β

/-- Dimensionless Gibbs entropy `log Z + β U`. -/
noncomputable def entropy (β : ℝ) : ℝ := Real.log (Z β) + β * internalEnergy β

/-- Dimensionless Helmholtz free energy `-(log Z)/β`. -/
noncomputable def freeEnergy (β : ℝ) : ℝ := -(Real.log (Z β)) / β

/-- The partition function used by the thermodynamic coordinates is strictly positive
on the honest Gibbs domain. -/
theorem Z_pos {β : ℝ} (hβ : 1 < β) : 0 < Z β := by
  unfold Z
  exact gibbsWeight_tsum_pos hβ

/-- The Massieu potential is exactly the entropy minus `β` times mean log-energy. -/
theorem entropy_sub_beta_mul_internalEnergy_eq_logZ (β : ℝ) :
    entropy β - β * internalEnergy β = Real.log (Z β) := by
  unfold entropy
  ring

/-- Away from the singular inverse-temperature coordinate, `βF = -log Z`. -/
theorem beta_mul_freeEnergy_eq_neg_logZ
    {β : ℝ} (hβ : β ≠ 0) :
    β * freeEnergy β = -Real.log (Z β) := by
  unfold freeEnergy
  field_simp [hβ] <;> ring

/-- Exact Legendre relation `F = U - S/β` away from the singular coordinate `β=0`. -/
theorem freeEnergy_eq_internalEnergy_sub_entropy_div
    {β : ℝ} (hβ : β ≠ 0) :
    freeEnergy β = internalEnergy β - entropy β / β := by
  unfold freeEnergy entropy
  field_simp [hβ] <;> ring

/-- Equivalent entropy/free-energy relation `S = β(U-F)` away from `β=0`. -/
theorem entropy_eq_beta_mul_internalEnergy_sub_freeEnergy
    {β : ℝ} (hβ : β ≠ 0) :
    entropy β = β * (internalEnergy β - freeEnergy β) := by
  unfold entropy freeEnergy
  field_simp [hβ] <;> ring

/-- Massieu/Legendre balance: `S + βF = βU`. -/
theorem entropy_add_beta_mul_freeEnergy_eq_beta_mul_internalEnergy
    {β : ℝ} (hβ : β ≠ 0) :
    entropy β + β * freeEnergy β = β * internalEnergy β := by
  rw [beta_mul_freeEnergy_eq_neg_logZ hβ]
  unfold entropy
  ring

/-- On `β>1` all thermodynamic coordinates use a positive partition function and both
forms of the Legendre relation are valid. -/
theorem gibbs_legendre_relation {β : ℝ} (hβ : 1 < β) :
    0 < Z β ∧
      freeEnergy β = internalEnergy β - entropy β / β ∧
      entropy β = β * (internalEnergy β - freeEnergy β) := by
  have hβ0 : β ≠ 0 := by linarith
  exact ⟨Z_pos hβ,
    freeEnergy_eq_internalEnergy_sub_entropy_div hβ0,
    entropy_eq_beta_mul_internalEnergy_sub_freeEnergy hβ0⟩

end GppZetaGibbsFreeEnergy

#print axioms GppZetaGibbsFreeEnergy.Z_pos
#print axioms GppZetaGibbsFreeEnergy.entropy_sub_beta_mul_internalEnergy_eq_logZ
#print axioms GppZetaGibbsFreeEnergy.beta_mul_freeEnergy_eq_neg_logZ
#print axioms GppZetaGibbsFreeEnergy.freeEnergy_eq_internalEnergy_sub_entropy_div
#print axioms GppZetaGibbsFreeEnergy.entropy_eq_beta_mul_internalEnergy_sub_freeEnergy
#print axioms GppZetaGibbsFreeEnergy.entropy_add_beta_mul_freeEnergy_eq_beta_mul_internalEnergy
#print axioms GppZetaGibbsFreeEnergy.gibbs_legendre_relation
