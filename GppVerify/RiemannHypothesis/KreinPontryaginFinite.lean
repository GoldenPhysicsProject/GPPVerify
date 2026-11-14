/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Flint (D3 seat), 2026-11-14, takeover shift for Claude Code's lane.

# The finite-dimensional Pontryagin core at `κ = 1`

Layer 1 of the Krein `κ = 1` build (Claude Code's scoping, 2026-11-14): the
finite-dimensional content of Krein's representation theorem for forms with at
most one negative square, stated in the tree's own vocabulary
(`GppKreinBridge.NoNegPlane`, the hypothesis of `GppKreinBridge.AtMostOneNegSq`).

For a symmetric bilinear form `B` on a real vector space, write `q x = B x x`.
Two facts, both pure algebra (no spectral theory, no analysis):

* `complement_quadratic_nonneg`: if `q u₀ < 0` and `q` has no negative 2-plane,
  then `q` is positive semidefinite on the `B`-orthogonal complement of `u₀`.
  Proof: a vector `x ⊥ u₀` with `q x < 0` would make the whole plane spanned by
  `x` and `u₀` negative at every nonzero combination, since the cross term
  vanishes — exactly what `NoNegPlane` forbids.

* `pontryagin_finite`: a symmetric form with no negative 2-plane is either
  positive semidefinite, or it splits along a negative direction `u₀` as
      `q x = q (x - t(x) • u₀) + t(x) * B(x, u₀)`,   `t(x) = B(x, u₀) / q u₀`,
  where the first term is `≥ 0` for every `x` and the second is a single
  negative square: `t(x) * B(x, u₀) = B(x, u₀)^2 / q u₀ ≤ 0` since `q u₀ < 0`.
  This is the finite-dimensional shadow of Krein's decomposition of a `κ = 1`
  kernel into a positive part plus an explicit one-dimensional negative
  (pole/ExpPart) part.

The remaining glue — applying this to the Gram form of a kernel configuration
(`kform K x`, symmetric once `K` is even) — is a separate, later step and is
not claimed here.

No `sorry`. No named premises. Standard axioms only.
-/
import GppVerify.RiemannHypothesis.KreinBridge

namespace GppKreinPontryaginFinite

open GppKreinBridge

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- If `q u₀ < 0` and `q` has no negative 2-plane, then `q` is nonnegative on
the `B`-orthogonal complement of `u₀`. -/
theorem complement_quadratic_nonneg {B : LinearMap.BilinForm ℝ V}
    (hsymm : ∀ x y, B x y = B y x) {u₀ : V} (hu : B u₀ u₀ < 0)
    (hNP : NoNegPlane (fun x => B x x)) {x : V} (hx : B x u₀ = 0) :
    0 ≤ B x x := by
  by_contra hlt
  rw [not_le] at hlt
  refine hNP x u₀ (fun a b hab => ?_)
  show B (a • x + b • u₀) (a • x + b • u₀) < 0
  have hux : B u₀ x = 0 := by rw [hsymm u₀ x]; exact hx
  have hexp : B (a • x + b • u₀) (a • x + b • u₀)
      = a * a * B x x + b * b * B u₀ u₀ := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hx, hux, mul_zero, add_zero, zero_add]
    ring
  rw [hexp]
  rcases hab with ha | hb
  · have h1 : a * a * B x x < 0 :=
      mul_neg_of_pos_of_neg (mul_self_pos.mpr ha) hlt
    have h2 : b * b * B u₀ u₀ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg b) hu.le
    linarith
  · have h1 : a * a * B x x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg a) hlt.le
    have h2 : b * b * B u₀ u₀ < 0 :=
      mul_neg_of_pos_of_neg (mul_self_pos.mpr hb) hu
    linarith

/-- **Finite-dimensional Pontryagin decomposition at `κ = 1`.** A symmetric
bilinear form with no negative 2-plane is either positive semidefinite, or it
splits along a negative direction `u₀` into a positive semidefinite part
(evaluated on the projection `x - (B x u₀ / B u₀ u₀) • u₀` onto the orthogonal
complement of `u₀`) plus the single negative square
`(B x u₀ / B u₀ u₀) * B x u₀ = B(x, u₀)^2 / B u₀ u₀`. -/
theorem pontryagin_finite {B : LinearMap.BilinForm ℝ V}
    (hsymm : ∀ x y, B x y = B y x)
    (hNP : NoNegPlane (fun x => B x x)) :
    (∀ x, 0 ≤ B x x) ∨
    ∃ u₀ : V, B u₀ u₀ < 0 ∧ ∀ x,
      0 ≤ B (x - (B x u₀ / B u₀ u₀) • u₀) (x - (B x u₀ / B u₀ u₀) • u₀) ∧
      B x x = B (x - (B x u₀ / B u₀ u₀) • u₀) (x - (B x u₀ / B u₀ u₀) • u₀)
        + (B x u₀ / B u₀ u₀) * B x u₀ := by
  by_cases h : ∀ x, 0 ≤ B x x
  · exact Or.inl h
  · push_neg at h
    obtain ⟨u₀, hu⟩ := h
    refine Or.inr ⟨u₀, hu, fun x => ?_⟩
    have hq : B u₀ u₀ ≠ 0 := ne_of_lt hu
    set t : ℝ := B x u₀ / B u₀ u₀ with ht_def
    have ht : t * B u₀ u₀ = B x u₀ := div_mul_cancel₀ _ hq
    have horth : B (x - t • u₀) u₀ = 0 := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      linarith
    refine ⟨complement_quadratic_nonneg hsymm hu hNP horth, ?_⟩
    have htsq : t ^ 2 * B u₀ u₀ = t * B x u₀ := by
      have h1 : t ^ 2 * B u₀ u₀ = t * (t * B u₀ u₀) := by ring
      rw [h1, ht]
    have hexp : B (x - t • u₀) (x - t • u₀)
        = B x x - 2 * t * B x u₀ + t ^ 2 * B u₀ u₀ := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hsymm u₀ x]
      ring
    rw [hexp, htsq]
    ring

end GppKreinPontryaginFinite
