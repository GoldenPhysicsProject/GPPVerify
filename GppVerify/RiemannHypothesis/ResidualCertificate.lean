import GppVerify.RiemannHypothesis.VariationalSchurScalar

/-!
# The arbitrary-predictor residual certificate for the variational Schur scalar

Source: Astra, `work/2026-10-23_astra_celestial_transfer_residual_extension.md` (GPP-bridge
`cfbc322`), extending `GppVariationalSchurScalar` (#417), which left this certificate
unformalized. Daniel Toupin / Golden Physics Project, with AI assistance from Astra (statements)
and Claude Code (formalization; written independently of Astra's uncompiled candidate).

Let `a` be a symmetric positive semidefinite bilinear form and `ℓ` a linear functional, with
`q_a(ℓ) = sup_v [2ℓ(v) − a(v, v)]`. Take **any** predictor `x` (no solve, no Galerkin equation),
and put `h = 2ℓ(x) − a(x, x)` and `r = ℓ − a(x, ·)`.

* `translate`: `2ℓ(x + w) − a(x + w, x + w) = h + 2r(w) − a(w, w)`.
* `bound_iff_residual`: `q` bounds the scalar of `ℓ` iff `q − h` bounds the scalar of `r`.
  This is the exact translation `q_a(ℓ) = h + q_a(r)`, stated with upper bounds.
* `bound_of_residual`: if `r(v)² ≤ e · a(v, v)` for all `v`, with `e ≥ 0`, then `h + e` bounds the
  scalar of `ℓ`.
* `block_nonneg_of_residual`: if moreover `h + e ≤ d`, the bordered form
  `a(u, u) + 2tℓ(u) + dt²` is nonnegative.

**Scope.** This is the certificate's algebra only. The actual arithmetic dual-residual estimate
(a usable `e` for the Weil coupling) is open, and is not assumed here. No claim about RH.
-/

namespace GppResidualCertificate

open GppVariationalSchurScalar

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The residual `r = ℓ − a(x, ·)` of the predictor `x`. -/
def residual (a : LinearMap.BilinForm ℝ V) (ℓ : V →ₗ[ℝ] ℝ) (x : V) : V →ₗ[ℝ] ℝ := ℓ - a x

/-- The predictor's value `h = 2ℓ(x) − a(x, x)`. -/
def value (a : LinearMap.BilinForm ℝ V) (ℓ : V →ₗ[ℝ] ℝ) (x : V) : ℝ := 2 * ℓ x - a x x

/-- **Exact translation.** -/
theorem translate (a : LinearMap.BilinForm ℝ V) (hsymm : ∀ u v, a u v = a v u)
    (ℓ : V →ₗ[ℝ] ℝ) (x w : V) :
    2 * ℓ (x + w) - a (x + w) (x + w) = value a ℓ x + (2 * residual a ℓ x w - a w w) := by
  simp only [value, residual, map_add, LinearMap.add_apply, LinearMap.sub_apply, hsymm w x]
  ring

/-- **`q_a(ℓ) = h + q_a(r)`**, as an equivalence of upper bounds. -/
theorem bound_iff_residual (a : LinearMap.BilinForm ℝ V) (hsymm : ∀ u v, a u v = a v u)
    (ℓ : V →ₗ[ℝ] ℝ) (x : V) (q : ℝ) :
    (∀ v, 2 * ℓ v - a v v ≤ q) ↔
      ∀ w, 2 * residual a ℓ x w - a w w ≤ q - value a ℓ x := by
  constructor
  · intro h w
    have := h (x + w)
    rw [translate a hsymm] at this
    linarith
  · intro h v
    have := h (v - x)
    have hv := translate a hsymm ℓ x (v - x)
    rw [add_sub_cancel] at hv
    linarith

/-- **Residual certificate.** `r(v)² ≤ e·a(v, v)` with `e ≥ 0` gives `q_a(ℓ) ≤ h + e`. -/
theorem bound_of_residual (a : LinearMap.BilinForm ℝ V) (hsymm : ∀ u v, a u v = a v u)
    (ha : ∀ u, 0 ≤ a u u) (ℓ : V →ₗ[ℝ] ℝ) (x : V) {e : ℝ} (he : 0 ≤ e)
    (hr : ∀ v, residual a ℓ x v ^ 2 ≤ e * a v v) :
    ∀ v, 2 * ℓ v - a v v ≤ value a ℓ x + e := by
  rw [bound_iff_residual a hsymm ℓ x, add_sub_cancel_left]
  exact (bound_iff a ha (residual a ℓ x) e).mpr ⟨he, hr⟩

/-- **Block certificate.** If also `h + e ≤ d`, the bordered form is nonnegative. -/
theorem block_nonneg_of_residual (a : LinearMap.BilinForm ℝ V) (hsymm : ∀ u v, a u v = a v u)
    (ha : ∀ u, 0 ≤ a u u) (ℓ : V →ₗ[ℝ] ℝ) (x : V) {e d : ℝ} (he : 0 ≤ e)
    (hr : ∀ v, residual a ℓ x v ^ 2 ≤ e * a v v) (hd : value a ℓ x + e ≤ d) :
    ∀ u : V, ∀ t : ℝ, 0 ≤ a u u + 2 * t * ℓ u + d * t ^ 2 :=
  (block_nonneg_iff_bound a ha ℓ d).mpr fun v =>
    (bound_of_residual a hsymm ha ℓ x he hr v).trans hd

end GppResidualCertificate
