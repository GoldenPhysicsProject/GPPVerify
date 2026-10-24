import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Isometric semigroups have positive-definite lag kernels

Source: Turbo, Wave 272 (GPP-bridge PR #11 comment 6377887735, structural lane) and the Wave 273–277
Gram scratch (`Wave276ScratchGram.lean`, not on the bridge). This is the finite Gram identity behind
the sign obstruction to the ground-state hypothesis (GS) of `GppGroundStateDetector` (#418). Daniel
Toupin / Golden Physics Project, with AI assistance from Turbo (statement) and Claude Code
(formalization, written independently of the scratch file).

* `gram_form_eq_norm_sq`: for vectors `w₁, …, w_n` and coefficients `c`,
  `∑_{i,j} conj(c_i) c_j ⟨w_i, w_j⟩ = ⟨∑_i c_i w_i, ∑_i c_i w_i⟩ = ‖∑_i c_i w_i‖²`.
* `gram_form_re_nonneg`: hence the Gram form is real and nonnegative.
* `semigroup_inner_shift`: for an isometric semigroup `V : ℕ → (E →ₗᵢ E)` with
  `V (s + d) = V d ∘ V s`, `⟨V s v, V (s + d) v⟩ = ⟨v, V d v⟩`. The proof uses that the semigroup is
  commutative (`V (s+d) = V (d+s)`) and that `V s` is an isometry. The lag kernel depends only
  on the lag.
* `semigroup_lag_kernel_psd`: so for times `t_i = s_i` and `f(d) = ⟨v, V d v⟩`, the matrix of
  `⟨V t_i v, V t_j v⟩` is a Gram matrix, and its form is nonnegative.

This is why a diagonal (GS) representation `K(t) = Re⟨v, V_t v⟩ + o(1)` with `V` an isometric
semigroup forces nonnegative Bohr coefficients, which contradicts the sign-alternating `R̃(γ)` Turbo
measured. **Scope.** Discrete time `ℕ` only. The continuous-time version, Bochner's theorem and the
Sz.-Nagy dilation step are not formalized. The sign data of `K` is numerical. No claim about RH.
-/

open Finset

namespace GppSemigroupGram

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Gram form = squared norm**, as the inner product of `∑ c_i w_i` with itself. -/
theorem gram_form_eq_norm_sq {n : ℕ} (w : Fin n → E) (c : Fin n → ℂ) :
    ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * @inner ℂ E _ (w i) (w j) =
      @inner ℂ E _ (∑ i, c i • w i) (∑ i, c i • w i) := by
  rw [sum_inner]
  refine sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

/-- **The Gram form is real and nonnegative.** -/
theorem gram_form_re_nonneg {n : ℕ} (w : Fin n → E) (c : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * @inner ℂ E _ (w i) (w j)).re := by
  rw [gram_form_eq_norm_sq]
  exact inner_self_nonneg (𝕜 := ℂ)

/-- **Lag invariance** for an isometric semigroup. -/
theorem semigroup_inner_shift (V : ℕ → E →ₗᵢ[ℂ] E)
    (hV : ∀ s d, V (s + d) = (V d).comp (V s)) (v : E) (s d : ℕ) :
    @inner ℂ E _ (V s v) (V (s + d) v) = @inner ℂ E _ v (V d v) := by
  rw [add_comm, hV d s, LinearIsometry.coe_comp, Function.comp_apply]
  exact (V s).inner_map_map v (V d v)

/-- **The lag kernel of an isometric semigroup is positive definite**: for any times `t` and
coefficients `c`, `Re ∑_{i,j} conj(c_i) c_j ⟨V t_i v, V t_j v⟩ ≥ 0`, where by
`semigroup_inner_shift` each entry with `t_i ≤ t_j` equals `⟨v, V (t_j − t_i) v⟩`. -/
theorem semigroup_lag_kernel_psd (V : ℕ → E →ₗᵢ[ℂ] E) (v : E) {n : ℕ} (t : Fin n → ℕ)
    (c : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * @inner ℂ E _ (V (t i) v) (V (t j) v)).re :=
  gram_form_re_nonneg (fun i => V (t i) v) c

end GppSemigroupGram
