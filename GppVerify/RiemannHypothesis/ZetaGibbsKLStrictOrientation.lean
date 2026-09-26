import GppVerify.RiemannHypothesis.BregmanStrictOrientationLocal
import GppVerify.RiemannHypothesis.ZetaGibbsFisherContinuity
import Mathlib.Tactic

/-!
# Strict directed-KL orientation for the zeta Gibbs family

This is the zeta-specific instantiation of the abstract local Bregman theorem.  It is
restricted throughout to the honest absolutely-convergent Gibbs domain `β>1`.
-/

namespace GppZetaGibbsKLStrictOrientation

open Set
open GppZetaGibbsInformationGeometry
open GppBregmanStrictOrientationLocal
open GppZetaGibbsThermodynamicDerivatives
open GppZetaGibbsFisher
open GppZetaGibbsFisherStrict
open GppZetaGibbsFisherContinuity

/-- Directed relative entropy of the zeta Gibbs family in its exact Bregman form. -/
noncomputable def zetaGibbsKL (β γ : ℝ) : ℝ :=
  bregmanKL zetaLogPartition zetaMeanEnergy β γ

/-- **Strict thermodynamic orientation of zeta Gibbs relative entropy.**
For `1 < β < γ`, the forward divergence is strictly larger than its reverse. -/
theorem zetaGibbsKL_gt_reverse
    {β γ : ℝ} (hβ : 1 < β) (hβγ : β < γ) :
    zetaGibbsKL γ β < zetaGibbsKL β γ := by
  have hA : ∀ x ∈ [[β, γ]],
      HasDerivAt zetaLogPartition (-zetaMeanEnergy x) x := by
    intro x hx
    have hxI : x ∈ Icc β γ := by
      simpa [uIcc_of_le hβγ.le] using hx
    exact hasDerivAt_zetaLogPartition (lt_of_lt_of_le hβ hxI.1)
  have hU : ∀ x ∈ [[β, γ]],
      HasDerivAt zetaMeanEnergy (-logEnergyVariance x) x := by
    intro x hx
    have hxI : x ∈ Icc β γ := by
      simpa [uIcc_of_le hβγ.le] using hx
    exact hasDerivAt_zetaMeanEnergy (lt_of_lt_of_le hβ hxI.1)
  have hgcont : ContinuousOn logEnergyVariance (Icc β γ) :=
    logEnergyVariance_continuousOn_Icc hβ hβγ.le
  have hganti : ∀ ⦃x y : ℝ⦄,
      β ≤ x → y ≤ γ → x < y → logEnergyVariance y < logEnergyVariance x := by
    intro x y hx hy hxy
    exact logEnergyVariance_strictAnti (lt_of_lt_of_le hβ hx) hxy
  unfold zetaGibbsKL
  exact bregmanKL_gt_reverse_of_fisher_strictAnti_local
    zetaLogPartition zetaMeanEnergy logEnergyVariance
    hβγ hA hU hgcont hganti

end GppZetaGibbsKLStrictOrientation

#print axioms GppZetaGibbsKLStrictOrientation.zetaGibbsKL_gt_reverse
