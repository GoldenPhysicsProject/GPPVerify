import GppVerify.RiemannHypothesis.BregmanTriangularKernel
import GppVerify.RiemannHypothesis.KLReflectionIdentity
import Mathlib.Tactic

/-!
# Strict orientation of one-parameter Gibbs Bregman divergences

A continuous Fisher metric which is strictly decreasing across an ordered parameter
interval gives a strict orientation to the two directed Bregman/KL divergences.
This is the exact abstract theorem needed by the zeta Gibbs family.
-/

namespace GppBregmanStrictOrientation

open Set MeasureTheory intervalIntegral
open GppZetaGibbsInformationGeometry
open GppBregmanTriangularKernel
open GppKLOrientationKernel
open GppKLReflectionIdentity

/-- **Strict Bregman/KL orientation from strict Fisher decrease.** -/
theorem bregmanKL_gt_reverse_of_fisher_strictAnti
    (A U g : ℝ → ℝ) {β γ : ℝ}
    (hβγ : β < γ)
    (hA : ∀ x ∈ [[β, γ]], HasDerivAt A (-U x) x)
    (hU : ∀ x ∈ [[β, γ]], HasDerivAt U (-g x) x)
    (hgcont : Continuous g)
    (hganti : ∀ ⦃x y : ℝ⦄, β ≤ x → y ≤ γ → x < y → g y < g x) :
    bregmanKL A U γ β < bregmanKL A U β γ := by
  have hcontOn : ContinuousOn g [[β, γ]] := hgcont.continuousOn
  rw [bregmanKL_eq_triangular A U g β γ hA hU hcontOn]
  rw [bregmanKL_reverse_eq_triangular A U g β γ hA hU hcontOn]
  have hsub :
      (∫ x in β..γ, (γ - x) * g x) -
          (∫ x in β..γ, (x - β) * g x) =
        ∫ x in β..γ, (β + γ - 2 * x) * g x := by
    rw [← intervalIntegral.integral_sub]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [lt_iff_sub_pos, hsub,
    antisymmetric_integral_eq_reflected g β γ hgcont]
  have hL : 0 < (γ - β) / 2 := by linarith
  apply reflectedKernel_integral_pos hL hgcont
  intro y hy
  have hxlo : β ≤ (β + γ) / 2 - y := by linarith
  have hyhi : (β + γ) / 2 + y ≤ γ := by linarith
  have hxy : (β + γ) / 2 - y < (β + γ) / 2 + y := by linarith
  exact hganti hxlo hyhi hxy

end GppBregmanStrictOrientation

#print axioms GppBregmanStrictOrientation.bregmanKL_gt_reverse_of_fisher_strictAnti
