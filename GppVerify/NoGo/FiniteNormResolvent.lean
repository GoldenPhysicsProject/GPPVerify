import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# A finite-norm boundary state cannot carry the completed response `m_*`

Source: Codex, GPP-bridge PR #11 comment 6123987713 (2026-10-12; note
`work/codex/2026-10-12_daniel_haar_peter_weyl_critical_line_discreteness.md`).

If `A` is accretive (`re⟪Ax, x⟫ ≥ 0`, for instance positive self-adjoint), `u > 0`, and
`(A + u)x = Ω`, then **`u · re⟪Ω, x⟫ ≤ ‖Ω‖²`** (`resolvent_diag_bound`). So any response of the form
`m(u) = ⟪Ω, (A + u)⁻¹ Ω⟫` with a finite-norm vector `Ω` has `u·m(u)` bounded
(`not_tendsto_atTop`).

The completed response `m_*(u) ~ log(√u/2π)/(4√u)` has `u·m_*(u) → ∞` by Stirling and the Euler
product. That asymptotic is Codex's and is **not** formalized here. Hence the sewing cannot be a
diagonal resolvent amplitude of a normalizable boundary state. It must be a trace, a
rigged/distributional boundary field, or a regularized relative determinant. **No RH claim.**
-/

namespace GppNoGo.FiniteNormResolvent

open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The diagonal resolvent bound.** -/
theorem resolvent_diag_bound (A : E →L[ℂ] E) (hA : ∀ x, 0 ≤ RCLike.re (inner ℂ (A x) x))
    {u : ℝ} (hu : 0 < u) {Ω x : E} (hx : A x + (u : ℂ) • x = Ω) :
    u * RCLike.re (inner ℂ Ω x) ≤ ‖Ω‖ ^ 2 := by
  have hre : RCLike.re (inner ℂ Ω x) = RCLike.re (inner ℂ (A x) x) + u * ‖x‖ ^ 2 := by
    rw [← hx, inner_add_left, inner_smul_left, map_add]
    simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  have hlow : u * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ Ω x) := by linarith [hA x]
  have hup : RCLike.re (inner ℂ Ω x) ≤ ‖Ω‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm Ω x)
  have hX := norm_nonneg x
  have hW := norm_nonneg Ω
  rcases hX.lt_or_eq with hpos | hzero
  · have hux : u * ‖x‖ ≤ ‖Ω‖ := by nlinarith
    nlinarith
  · rw [← hzero] at hup
    nlinarith

/-- **No finite-norm boundary state.** If `m(u) = re⟪Ω, x_u⟫` with `(A + u)x_u = Ω` for all
`u > 0`, then `u·m(u)` does not tend to `+∞`. -/
theorem not_tendsto_atTop (A : E →L[ℂ] E) (hA : ∀ x, 0 ≤ RCLike.re (inner ℂ (A x) x)) (Ω : E)
    (xu : ℝ → E) (hxu : ∀ u, 0 < u → A (xu u) + (u : ℂ) • xu u = Ω) (m : ℝ → ℝ)
    (hm : ∀ u, 0 < u → m u = RCLike.re (inner ℂ Ω (xu u))) :
    ¬ Tendsto (fun u => u * m u) atTop atTop := by
  intro h
  obtain ⟨u, hu⟩ := ((h.eventually (eventually_gt_atTop (‖Ω‖ ^ 2))).and
    (eventually_gt_atTop 0)).exists
  have := resolvent_diag_bound A hA hu.2 (hxu u hu.2)
  rw [← hm u hu.2] at this
  linarith [hu.1]

end GppNoGo.FiniteNormResolvent
