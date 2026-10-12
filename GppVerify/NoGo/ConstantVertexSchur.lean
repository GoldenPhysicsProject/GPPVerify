import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral

/-!
# Constant-vertex Schur models: the Gaussian moment and both regimes

Source: Codex, GPP-bridge PR #11 comment 6124261472 (2026-10-12). Codex proposed a "stronger F_θ
kill test": couple the `K`-trivial and conductor-3 sectors on `L²(ℝ, dw)`, `w = log|x|`, through a
constant vertex twisted by `e^{θw}`. On Gaussian translates `φ_L = π^{−1/4}e^{−(w−L)²/2}` the
coupling term is `⟨φ_L, e^{κw} φ_L⟩ = e^{κL + κ²/4}` (`gauss_moment`, proved here for every real
`κ`).

* `twisted_form_tendsto_atBot`: with a constant vertex and `κ = θ > 0`, the quadratic form
  `C − e^{θL+θ²/4}` tends to `−∞`, for any constant kinetic-plus-mass term `C`. The constant-vertex
  model is not semibounded.
* `decaying_moment_tendsto_zero`: with the vertex that actually comes from ζ's prime measure
  `Σ Λ(n) n^{−1/2} δ_{log n}` (half-density weight `e^{−w/2}`), F_θ's twist `2cosh(θw)` gives
  `κ = θ − ½ < 0` for `θ < ½`. Then the moment tends to `0`, and **no** such unboundedness occurs.

**Ledger reading (Claude Code audit, comment 6124273075).** This kills the *constant-vertex* Schur
model. It does **not** discriminate ζ from F_θ for a vertex derived from ζ's own data. That
discrimination lives in the balanced explicit-formula cancellation (Claude Code note
`work/claude-code/2026-10-12_loewner_mstar_vs_ftheta.md`). The kinetic term `⟨φ, D²φ⟩ = ½` is
not formalized here; it enters only as the constant `C`. **No RH claim.**
-/

namespace GppNoGo.ConstantVertexSchur

open Real MeasureTheory Filter

/-- **The Gaussian moment.** `∫ e^{−(w−L)²} e^{κw} dw = √π · e^{κL + κ²/4}`. -/
theorem gauss_moment (κ L : ℝ) :
    ∫ w : ℝ, exp (-(w - L) ^ 2) * exp (κ * w) = sqrt π * exp (κ * L + κ ^ 2 / 4) := by
  have hpt : ∀ w : ℝ, exp (-(w - L) ^ 2) * exp (κ * w) =
      exp (κ * L + κ ^ 2 / 4) * exp (-1 * (w - (L + κ / 2)) ^ 2) := by
    intro w
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub_right_eq_self (fun w => exp (-1 * w ^ 2)) (L + κ / 2),
    integral_gaussian]
  simp [mul_comm]

/-- **Constant vertex, `θ > 0`: the form is unbounded below.** -/
theorem twisted_form_tendsto_atBot {θ : ℝ} (hθ : 0 < θ) (C : ℝ) :
    Tendsto (fun L : ℝ => C - exp (θ * L + θ ^ 2 / 4)) atTop atBot := by
  have h : Tendsto (fun L : ℝ => -exp (θ * L + θ ^ 2 / 4)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_exp_atTop.comp
      (tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hθ)))
  simpa [sub_eq_add_neg] using tendsto_atBot_add_const_left atTop C h

/-- **Vertex derived from ζ's prime weights (`κ = θ − ½ < 0`): the moment tends to `0`.** -/
theorem decaying_moment_tendsto_zero {κ : ℝ} (hκ : κ < 0) :
    Tendsto (fun L : ℝ => exp (κ * L + κ ^ 2 / 4)) atTop (nhds 0) := by
  apply tendsto_exp_atBot.comp
  exact tendsto_atBot_add_const_right _ _ (tendsto_id.const_mul_atTop_of_neg hκ)

end GppNoGo.ConstantVertexSchur
