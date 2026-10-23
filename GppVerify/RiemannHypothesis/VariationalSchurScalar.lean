import GppVerify.RiemannHypothesis.ScalarSchurForm
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The variational Schur scalar, with no inverse and no coercivity

Source: Astra, `work/2026-10-23_astra_schur_variational_frontier.md` §1–§2 and
`work/2026-10-23_astra_actual_arithmetic_residual.md` (GPP-bridge), adopted by Turbo as the
domain-safe form of the (RES) step. Daniel Toupin / Golden Physics Project, with AI assistance
from Astra (statements) and Claude Code (formalization).

For a positive semidefinite symmetric bilinear form `a` and a linear functional `ℓ`, Astra's scalar
is `q_a(ℓ) = sup_v [2 ℓ(v) − a(v, v)]`. This file proves the facts that make it usable without a
bounded inverse, stated with `q` as an upper bound so that no supremum has to be constructed:

* `bound_iff`: `2 ℓ(v) − a(v, v) ≤ q` for all `v` iff `0 ≤ q` and `ℓ(v)² ≤ q · a(v, v)` for all `v`.
  So `q_a(ℓ)` is the squared dual norm of `ℓ` in the `a`-seminorm, infinite when `ℓ` is nonzero on
  the null space of `a`.
* `block_nonneg_iff_bound`: the bordered form `a(u, u) + 2 t ℓ(u) + d t²` is nonnegative iff
  `2 ℓ(v) − a(v, v) ≤ d` for all `v`, i.e. block positivity ⇔ `q_a(ℓ) ≤ d`.
* `bound_of_le`: if `a ≤ a'` pointwise then any bound for `a` is a bound for `a'`, so the scalar can
  only drop when the form grows.
* `rankOne_left_inv`, `rankOne_right_inv`: Astra's calibration. On a real inner product space,
  `P x = x − c ⟨e, x⟩ e` with `⟨e, e⟩ = L`, `cL ≠ 1`, has inverse `x + (c/(1 − cL)) ⟨e, x⟩ e`. On
  `L²(0, L)` with `e = 1` this is `P_L = I − c|1⟩⟨1|`, whose inverse kernel carries `δ(u − v)`.

**Scope.** Finite-dimensional approximation (`q_n ↑ q_a`), the range characterisation
`q_A(b) = ‖A^{−1/2} b‖²` in Hilbert space, and the form-dual residual certificate are not
formalized. The unpaid input Astra names, a form-dual bound for the actual arithmetic coupling, is
the open mathematics. No claim about RH.
-/

namespace GppVariationalSchurScalar

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The variational scalar is the squared dual norm.** -/
theorem bound_iff (a : LinearMap.BilinForm ℝ V) (ha : ∀ u, 0 ≤ a u u) (ℓ : V →ₗ[ℝ] ℝ) (q : ℝ) :
    (∀ v, 2 * ℓ v - a v v ≤ q) ↔ (0 ≤ q ∧ ∀ v, ℓ v ^ 2 ≤ q * a v v) := by
  constructor
  · intro h
    refine ⟨by simpa using h 0, fun v => ?_⟩
    have hq : ∀ t : ℝ, 0 ≤ a v v * (t * t) + (-(2 * ℓ v)) * t + q := fun t => by
      have := h (t • v)
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      nlinarith
    have hd := discrim_le_zero hq
    unfold discrim at hd
    nlinarith
  · rintro ⟨hq, hL⟩ v
    nlinarith [hL v, ha v, sq_nonneg (q - a v v), sq_nonneg (2 * ℓ v - q - a v v)]

/-- **Block positivity ⇔ `q_a(ℓ) ≤ d`.** -/
theorem block_nonneg_iff_bound (a : LinearMap.BilinForm ℝ V) (ha : ∀ u, 0 ≤ a u u)
    (ℓ : V →ₗ[ℝ] ℝ) (d : ℝ) :
    (∀ u : V, ∀ t : ℝ, 0 ≤ a u u + 2 * t * ℓ u + d * t ^ 2) ↔ ∀ v, 2 * ℓ v - a v v ≤ d := by
  rw [GppScalarSchurForm.nonneg_iff a ha ℓ d, bound_iff a ha ℓ d]

/-- **Monotonicity.** Enlarging the form can only lower the variational scalar. -/
theorem bound_of_le (a a' : LinearMap.BilinForm ℝ V) (haa : ∀ v, a v v ≤ a' v v)
    (ℓ : V →ₗ[ℝ] ℝ) (q : ℝ) (h : ∀ v, 2 * ℓ v - a v v ≤ q) : ∀ v, 2 * ℓ v - a' v v ≤ q :=
  fun v => by linarith [h v, haa v]

section RankOne

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Rank-one calibration, left inverse.** -/
theorem rankOne_left_inv (e : E) (c L : ℝ) (he : @inner ℝ E _ e e = L) (hcL : c * L ≠ 1)
    (x : E) :
    let y := x + (c / (1 - c * L) * @inner ℝ E _ e x) • e
    y - (c * @inner ℝ E _ e y) • e = x := by
  intro y
  have h1 : 1 - c * L ≠ 0 := sub_ne_zero.mpr (Ne.symm hcL)
  have hy : @inner ℝ E _ e y = @inner ℝ E _ e x / (1 - c * L) := by
    simp only [y, inner_add_right, inner_smul_right, he]
    field_simp
    ring
  simp only [y, hy, add_sub_assoc, ← sub_smul]
  rw [show c / (1 - c * L) * @inner ℝ E _ e x - c * (@inner ℝ E _ e x / (1 - c * L)) = 0 by ring,
    zero_smul, add_zero]

/-- **Rank-one calibration, right inverse.** -/
theorem rankOne_right_inv (e : E) (c L : ℝ) (he : @inner ℝ E _ e e = L) (hcL : c * L ≠ 1)
    (x : E) :
    let y := x - (c * @inner ℝ E _ e x) • e
    y + (c / (1 - c * L) * @inner ℝ E _ e y) • e = x := by
  intro y
  have h1 : 1 - c * L ≠ 0 := sub_ne_zero.mpr (Ne.symm hcL)
  have hy : @inner ℝ E _ e y = (1 - c * L) * @inner ℝ E _ e x := by
    simp only [y, inner_sub_right, inner_smul_right, he]
    ring
  simp only [y, hy, sub_add_eq_add_sub, add_sub_assoc, ← sub_smul]
  rw [show c / (1 - c * L) * ((1 - c * L) * @inner ℝ E _ e x) - c * @inner ℝ E _ e x = 0 by
    field_simp; ring, zero_smul, add_zero]

end RankOne

end GppVariationalSchurScalar
