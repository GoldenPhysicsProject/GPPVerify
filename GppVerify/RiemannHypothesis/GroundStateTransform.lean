import Mathlib.Tactic

/-!
# Finite positive-ground-state transform and Poincaré transport

Source: Codex, GPP-bridge PR #11 handoff of 2026-10-30 22:31Z (Priority 1: finite
positive-ground-state transform), building on the edge identity in `GroundStatePicone.lean`.
Daniel Toupin / Golden Physics Project, with AI assistance from Codex (statement) and Claude Code
(formalization).

Let `X` be a finite type, `w : X → X → ℝ` a symmetric weight, `V : X → ℝ` a potential and
`(Hψ)(x) = V x · ψ x − Σ_y w x y · ψ y`. If `φ` satisfies `Hφ = E₀ φ`, then for every real `f`:

* `transformed_apply`: `((H − E₀)(φ f))(x) = Σ_y w x y φ y (f x − f y)`.
* `picone_form_identity`: `Σ_x φ f ((H − E₀)(φ f)) = ½ Σ_{x,y} w x y φ x φ y (f x − f y)²`.
* `picone_form_nonneg`: if `w ≥ 0` the form is `≥ 0`, with no sign assumption on `f` or on `φ`.
* `poincare_transport`: a Poincaré inequality `Var_{φ²}(f) ≤ C · D(f)` for the weighted Dirichlet
  form `D(f) = ½ Σ w φ φ (f x − f y)²` gives, for every `ψ` orthogonal to `φ`,
  `Σ ψ² ≤ C · ⟨ψ, (H − E₀) ψ⟩`, via the bijection `f = ψ / φ` (needs `φ > 0` pointwise).

**Scope.** Real scalars and a finite state space only. The complex case follows by splitting real
and imaginary parts and is not formalized here. No uniqueness of the ground state, positivity of
`w`, or unit normalisation of `φ` is needed for the identity itself; positivity of `w` is only used
for `picone_form_nonneg`. The Poincaré inequality is a hypothesis: no claim is made about any
uniform-in-volume constant `C` (the exact stress test of the same handoff shows global residual
oscillation is not volume robust). Not a gap certificate for any Yang–Mills Hamiltonian. No claim
about RH.
-/

set_option autoImplicit false

open Finset

namespace GppGroundStateTransform

variable {X : Type*} [Fintype X]

/-- `(Hψ)(x) = V x · ψ x − Σ_y w x y · ψ y`. -/
def applyH (V : X → ℝ) (w : X → X → ℝ) (ψ : X → ℝ) (x : X) : ℝ :=
  V x * ψ x - ∑ y, w x y * ψ y

/-- Weighted Dirichlet form `D_φ(f) = ½ Σ_{x,y} w x y φ x φ y (f x − f y)²`. -/
noncomputable def dirichlet (w : X → X → ℝ) (φ f : X → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, w x y * φ x * φ y * (f x - f y) ^ 2

/-- The transformed operator acts as a weighted graph Laplacian on `f`. -/
theorem transformed_apply {V : X → ℝ} {w : X → X → ℝ} {φ : X → ℝ} {E₀ : ℝ}
    (hφ : ∀ x, applyH V w φ x = E₀ * φ x) (f : X → ℝ) (x : X) :
    applyH V w (fun z => φ z * f z) x - E₀ * (φ x * f x) =
      ∑ y, w x y * φ y * (f x - f y) := by
  have h := hφ x
  unfold applyH at h ⊢
  have e1 : ∑ y, w x y * φ y * (f x - f y) =
      f x * ∑ y, w x y * φ y - ∑ y, w x y * (φ y * f y) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
  rw [e1]
  linear_combination f x * h

/-- **The Picone form identity.** -/
theorem picone_form_identity {V : X → ℝ} {w : X → X → ℝ} {φ : X → ℝ} {E₀ : ℝ}
    (hw : ∀ x y, w x y = w y x) (hφ : ∀ x, applyH V w φ x = E₀ * φ x) (f : X → ℝ) :
    ∑ x, φ x * f x * (applyH V w (fun z => φ z * f z) x - E₀ * (φ x * f x)) =
      dirichlet w φ f := by
  have h1 : ∑ x, φ x * f x * (applyH V w (fun z => φ z * f z) x - E₀ * (φ x * f x)) =
      ∑ x, ∑ y, w x y * φ x * φ y * (f x * (f x - f y)) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [transformed_apply hφ f x, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
  have h2 : ∑ x, ∑ y, w x y * φ x * φ y * (f x * (f x - f y)) =
      ∑ x, ∑ y, w x y * φ x * φ y * (f y * (f y - f x)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [hw x y]
    ring
  have h3 : ∑ x, ∑ y, w x y * φ x * φ y * (f x - f y) ^ 2 =
      ∑ x, ∑ y, w x y * φ x * φ y * (f x * (f x - f y)) +
      ∑ x, ∑ y, w x y * φ x * φ y * (f y * (f y - f x)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
  unfold dirichlet
  rw [h1]
  linarith [h2, h3]

/-- With nonnegative weights and `φ` a positive-ground-state certificate, the transformed form
is nonnegative for every real `f`. -/
theorem picone_form_nonneg {V : X → ℝ} {w : X → X → ℝ} {φ : X → ℝ} {E₀ : ℝ}
    (hw : ∀ x y, w x y = w y x) (hw0 : ∀ x y, 0 ≤ w x y) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφ : ∀ x, applyH V w φ x = E₀ * φ x) (f : X → ℝ) :
    0 ≤ ∑ x, φ x * f x * (applyH V w (fun z => φ z * f z) x - E₀ * (φ x * f x)) := by
  rw [picone_form_identity hw hφ f]
  unfold dirichlet
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
  have := hw0 x y
  have := hφ0 x
  have := hφ0 y
  positivity

/-- **Poincaré transport.** A Poincaré inequality for the measure `φ²` transports to the quadratic
form `⟨ψ, (H − E₀) ψ⟩` on vectors orthogonal to `φ`, via `f = ψ / φ`. -/
theorem poincare_transport {V : X → ℝ} {w : X → X → ℝ} {φ : X → ℝ} {E₀ C : ℝ}
    (hw : ∀ x y, w x y = w y x) (hφ : ∀ x, applyH V w φ x = E₀ * φ x) (hpos : ∀ x, 0 < φ x)
    (hP : ∀ f : X → ℝ, ∑ x, φ x ^ 2 * f x ^ 2 - (∑ x, φ x ^ 2 * f x) ^ 2 ≤
      C * dirichlet w φ f)
    (ψ : X → ℝ) (horth : ∑ x, φ x * ψ x = 0) :
    ∑ x, ψ x ^ 2 ≤ C * ∑ x, ψ x * (applyH V w ψ x - E₀ * ψ x) := by
  set f : X → ℝ := fun x => ψ x / φ x with hf
  have hpf : ∀ x, φ x * f x = ψ x := fun x => by
    rw [hf]; field_simp [(hpos x).ne']
  have h1 : ∑ x, φ x ^ 2 * f x ^ 2 = ∑ x, ψ x ^ 2 :=
    Finset.sum_congr rfl fun x _ => by rw [← hpf x]; ring
  have h2 : ∑ x, φ x ^ 2 * f x = 0 := by
    rw [← horth]; refine Finset.sum_congr rfl fun x _ => ?_
    rw [← hpf x]; ring
  have key := picone_form_identity hw hφ f
  simp only [hpf] at key
  have hP' := hP f
  rw [h1, h2] at hP'
  rw [key]
  simpa using hP'

end GppGroundStateTransform
