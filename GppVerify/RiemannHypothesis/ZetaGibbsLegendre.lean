import GppVerify.RiemannHypothesis.ZetaGibbsFisher
import Mathlib.Tactic

/-!
# Legendre thermodynamics of the zeta Gibbs gas

This file completes the algebraic thermodynamic dictionary on the honest Gibbs
domain `β > 1`.  With partition function `Z`, internal energy `U = M1/Z`,
Helmholtz free energy `F = -(log Z)/β`, and entropy

  S = log Z + β U,

the standard Legendre identities are exact.  No analytic continuation or RH
input is involved.
-/

namespace GppZetaGibbsLegendre

open GppZetaGibbsSummability GppZetaGibbsFisher

/-- Gibbs internal energy for the logarithmic arithmetic Hamiltonian. -/
noncomputable def internalEnergy (β : ℝ) : ℝ := M1 β / Z β

/-- Dimensionless Helmholtz free energy. -/
noncomputable def freeEnergy (β : ℝ) : ℝ := -Real.log (Z β) / β

/-- Dimensionless Gibbs entropy. -/
noncomputable def entropy (β : ℝ) : ℝ :=
  Real.log (Z β) + β * internalEnergy β

/-- The zeta Gibbs partition function is strictly positive throughout its
absolute-convergence domain. -/
theorem partition_pos {β : ℝ} (hβ : 1 < β) : 0 < Z β := by
  simpa [Z] using gibbsWeight_tsum_pos hβ

/-- The free-energy definition in multiplicative form. -/
theorem beta_mul_freeEnergy {β : ℝ} (hβ : 1 < β) :
    β * freeEnergy β = -Real.log (Z β) := by
  have hβ0 : β ≠ 0 := ne_of_gt (lt_trans (by norm_num) hβ)
  unfold freeEnergy
  field_simp [hβ0]

/-- Exact entropy/free-energy Legendre identity. -/
theorem entropy_eq_beta_mul_internal_sub_free {β : ℝ} (hβ : 1 < β) :
    entropy β = β * (internalEnergy β - freeEnergy β) := by
  rw [entropy]
  have hF := beta_mul_freeEnergy hβ
  linarith

/-- Equivalent Helmholtz identity `F = U - S/β`. -/
theorem freeEnergy_eq_internal_sub_entropy_div_beta
    {β : ℝ} (hβ : 1 < β) :
    freeEnergy β = internalEnergy β - entropy β / β := by
  have hβ0 : β ≠ 0 := ne_of_gt (lt_trans (by norm_num) hβ)
  have hS := entropy_eq_beta_mul_internal_sub_free hβ
  field_simp [hβ0]
  linarith

/-- The entropy response already formalized in `ZetaGibbsFisher` is the
thermodynamic susceptibility `-β Var(log n)` on the Gibbs axis. -/
theorem entropy_response_eq_neg_beta_variance (β : ℝ) :
    entropyBetaDerivative β = -β * logEnergyVariance β := by
  rfl

/-- Heat capacity and entropy response are tied by the exact fluctuation
identity `β * S'(β) = -C(β)`. -/
theorem beta_mul_entropy_response_eq_neg_heatCapacity (β : ℝ) :
    β * entropyBetaDerivative β = -heatCapacity β := by
  unfold entropyBetaDerivative heatCapacity
  ring

/-- Consequently `β*S'(β) ≤ 0` on the Gibbs domain. -/
theorem beta_mul_entropy_response_nonpos {β : ℝ} (hβ : 1 < β) :
    β * entropyBetaDerivative β ≤ 0 := by
  rw [beta_mul_entropy_response_eq_neg_heatCapacity]
  exact neg_nonpos.mpr (heatCapacity_nonneg hβ)

end GppZetaGibbsLegendre

#print axioms GppZetaGibbsLegendre.partition_pos
#print axioms GppZetaGibbsLegendre.beta_mul_freeEnergy
#print axioms GppZetaGibbsLegendre.entropy_eq_beta_mul_internal_sub_free
#print axioms GppZetaGibbsLegendre.freeEnergy_eq_internal_sub_entropy_div_beta
#print axioms GppZetaGibbsLegendre.beta_mul_entropy_response_eq_neg_heatCapacity
