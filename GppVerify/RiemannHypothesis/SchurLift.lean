import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Abstract low/high Schur lift

Source: Codex/Discovery2, GPP-bridge PR #11 comments 2026-10-31 (full completed Weil positivity
via "finite-low / infinite-high one-sided Schur": the high block is `≥ d·I`, it couples to the low
block only through a cross term, and a finite Schur complement is positive). Daniel Toupin / Golden
Physics Project, with AI assistance from Codex (statement) and Claude Code (formalization).

For a real inner product space `F` (the high block), a normed space `E` (the low block), a quadratic
part `a : E → ℝ`, a cross vector `u : E → F`, and a high quadratic part `c : F → ℝ` with
`c y ≥ d‖y‖²`:

* `schur_pointwise`: `−‖u‖²/(d−δ) ≤ (d−δ)‖y‖² + 2⟪u, y⟫` for `δ < d`.
* `schur_lift`: if the finite Schur condition `δ‖x‖² + ‖u x‖²/(d−δ) ≤ a x` holds for all `x`, then
  `δ(‖x‖² + ‖y‖²) ≤ a x + 2⟪u x, y⟫ + c y` for all `x, y`.

**Scope.** The abstract completion of the square only: no Weil form, no Legendre spectrum, no
checking of the Schur condition (that is where Codex's Arb/LDL certificates enter, and they are not
formalized). Complex forms are handled by realification and are not treated here. No claim about RH.
-/

set_option autoImplicit false

namespace GppSchurLift

/-- Completion of the square: `−‖u‖²/(d−δ) ≤ (d−δ)‖y‖² + 2⟪u, y⟫` when `δ < d`. -/
theorem schur_pointwise {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {d δ : ℝ}
    (h : δ < d) (u y : F) :
    -(‖u‖ ^ 2 / (d - δ)) ≤ (d - δ) * ‖y‖ ^ 2 + 2 * inner ℝ u y := by
  have hp : 0 < d - δ := by linarith
  have hsq : 0 ≤ ‖(d - δ) • y + u‖ ^ 2 := by positivity
  have hexp : ‖(d - δ) • y + u‖ ^ 2 =
      (d - δ) ^ 2 * ‖y‖ ^ 2 + 2 * (d - δ) * inner ℝ u y + ‖u‖ ^ 2 := by
    rw [@norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_smul_left]
    simp only [RCLike.conj_to_real]
    rw [real_inner_comm]
    ring
  rw [neg_div', div_le_iff₀ hp]
  nlinarith [hsq, hexp]

/-- The abstract Schur lift. -/
theorem schur_lift {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {d δ : ℝ} (hδ : δ < d) (a c : _ → ℝ) (u : E → F)
    (hc : ∀ y : F, d * ‖y‖ ^ 2 ≤ c y)
    (hS : ∀ x : E, δ * ‖x‖ ^ 2 + ‖u x‖ ^ 2 / (d - δ) ≤ a x) (x : E) (y : F) :
    δ * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ a x + 2 * inner ℝ (u x) y + c y := by
  have h1 := schur_pointwise hδ (u x) y
  have h2 := hc y
  have h3 := hS x
  nlinarith [h1, h2, h3]

end GppSchurLift
