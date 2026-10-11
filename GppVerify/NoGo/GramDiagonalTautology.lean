import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# No-go: an off-diagonal lower bound from Gram positivity carries no arithmetic

**Strategy refuted.** "The cross-prime part of the window energy `∫ w_H |J|²` is bounded below by
`−B(σ) − D_σ/H²`, uniformly in the centre `T` — a genuine prime-side signed inequality."
(Codex, GPP-bridge PR #11, 2026-10-08, "uniform pointwise O(1) cross-prime lower bound".)

**Theorem (`offDiag_re_ge_neg_diag`).** For *any* finite family of vectors `vᵢ` in *any* complex inner
product space, `Re ∑_{i≠j} ⟪vᵢ, vⱼ⟫ ≥ −∑ᵢ ‖vᵢ‖²`. The cross-prime bound is this inequality with
`vᵢ = Λ(nᵢ) nᵢ^{−σ} e^{−i t log nᵢ}` in `L²(w_H)`; nothing about primes enters except finiteness of the
diagonal. So it is not evidence toward a Weil-type inequality.

**What the no-go leaves open (the hint).** Arithmetic content must enter through a *signed* or
*upper* bound on the off-diagonal, or through a Gram matrix whose entries already contain the linear
Weil coefficient and the pole/Archimedean terms (as in `Q_L = B_L − 2|v⟩⟨v|`, `OddCollisionTrace`).
-/

open scoped InnerProductSpace

namespace GppNoGo.GramDiagonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `0 ≤ ‖∑ vᵢ‖² = ∑ᵢ ‖vᵢ‖² + Re ∑_{i≠j} ⟪vᵢ, vⱼ⟫`, rearranged. -/
theorem offDiag_re_ge_neg_diag {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → E) :
    -(∑ i ∈ s, ‖v i‖ ^ 2) ≤ (∑ i ∈ s, ∑ j ∈ s.erase i, ⟪v i, v j⟫_ℂ).re := by
  have hnorm : (‖∑ i ∈ s, v i‖ ^ 2 : ℝ) = (∑ i ∈ s, ∑ j ∈ s, ⟪v i, v j⟫_ℂ).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner]
    simp_rw [inner_sum]
    rfl
  have hsplit : (∑ i ∈ s, ∑ j ∈ s, ⟪v i, v j⟫_ℂ)
      = (∑ i ∈ s, ⟪v i, v i⟫_ℂ) + ∑ i ∈ s, ∑ j ∈ s.erase i, ⟪v i, v j⟫_ℂ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← Finset.add_sum_erase s _ hi]
  have hdiag : (∑ i ∈ s, ⟪v i, v i⟫_ℂ).re = ∑ i ∈ s, ‖v i‖ ^ 2 := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun i _ => inner_self_eq_norm_sq (𝕜 := ℂ) (v i))
  have h0 : (0 : ℝ) ≤ ‖∑ i ∈ s, v i‖ ^ 2 := by positivity
  rw [hnorm, hsplit, Complex.add_re, hdiag] at h0
  linarith

end GppNoGo.GramDiagonal
