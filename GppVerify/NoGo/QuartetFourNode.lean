import GppVerify.NoGo.QuartetSignature
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Realisation: an off-axis quartet has two negative squares at **every** four distinct real nodes

Codex (GPP-bridge PR #11, 2026-10-11) observed that `N(x,y) = v(x)ᵀ C v(y)` with `v = (1,x,x²,x³)`, so
the 4×4 real-node Pick matrix is congruent to `C` through an invertible Vandermonde matrix. Combined
with the signature theorem `GppNoGo.QuartetSignature.Q_neg_plane`, this gives:

**Theorem (`two_negative_at_four_nodes`).** If `h > 0`, `w > 0` and `x₁,…,x₄ > 0` are distinct, there
are weight vectors `c₁, c₂` such that the Pick form `∑ᵢⱼ cᵢcⱼ K(xᵢ,xⱼ)` is strictly negative on every
nonzero combination `αc₁ + βc₂`. So the negative index is ≥ 2 already at four nodes; with the
`(2,2)` signature of `Q` it is exactly 2.

**Hint.** Off-axis zeros are detected at size 4 with no choice of nodes needed; what decides RH is
whether, in the *sum over all quartets*, on-line positive mass can mask these directions, which is the
Weil-positivity question.
-/

namespace GppNoGo.QuartetFourNode

open GppNoGo.QuartetThreeNode GppNoGo.QuartetSignature Matrix

theorem moments_eq (x u : Fin 4 → ℝ) (k : Fin 4) :
    ∑ i, u i * x i ^ (k : ℕ) = ((vandermonde x)ᵀ *ᵥ u) k := by
  simp [mulVec, dotProduct, vandermonde_apply, mul_comm]

/-- **Two negative squares at every four distinct positive nodes.** -/
theorem two_negative_at_four_nodes {h w : ℝ} (hh : 0 < h) (hw : 0 < w) (x : Fin 4 → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) :
    ∃ c₁ c₂ : Fin 4 → ℝ, ∀ α β : ℝ, (α ≠ 0 ∨ β ≠ 0) →
      ∑ i, ∑ j, (α * c₁ i + β * c₂ i) * (α * c₁ j + β * c₂ j) * K h w (x i) (x j) < 0 := by
  set M : Matrix (Fin 4) (Fin 4) ℝ := (vandermonde x)ᵀ with hM
  have hdet : IsUnit M.det := by
    rw [hM, det_transpose]
    exact (det_vandermonde_ne_zero_iff.mpr hinj).isUnit
  set e : Fin 4 → ℝ := ![1, 0, -(h ^ 2 + w) / h, 0]
  set o : Fin 4 → ℝ := ![0, 1, 0, -h]
  set u₁ := M⁻¹ *ᵥ e
  set u₂ := M⁻¹ *ᵥ o
  have hu₁ : M *ᵥ u₁ = e := by rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hu₂ : M *ᵥ u₂ = o := by rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  refine ⟨fun i => D h w (x i) * u₁ i, fun i => D h w (x i) * u₂ i, fun α β hαβ => ?_⟩
  set u : Fin 4 → ℝ := fun i => α * u₁ i + β * u₂ i
  have hform : ∑ i, ∑ j, (α * (D h w (x i) * u₁ i) + β * (D h w (x i) * u₂ i))
      * (α * (D h w (x j) * u₁ j) + β * (D h w (x j) * u₂ j)) * K h w (x i) (x j)
      = 4 * ∑ i, ∑ j, u i * u j * N h w (x i) (x j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [K_eq hh hw.le (hx i) (hx j)]
    have hDi := (D_pos (x := x i) hh hw.le).ne'
    have hDj := (D_pos (x := x j) hh hw.le).ne'
    simp only [u]
    field_simp
  rw [hform, sum_N_eq_Q]
  have hE : ∀ k : Fin 4, ∑ i, u i * x i ^ (k : ℕ) = α * e k + β * o k := by
    intro k
    rw [moments_eq, show u = α • u₁ + β • u₂ from rfl, mulVec_add, mulVec_smul, mulVec_smul, hu₁, hu₂]
    rfl
  have h0 := hE 0
  have h1 := hE 1
  have h2 := hE 2
  have h3 := hE 3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, mul_one, pow_one, e, o,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2 h3
  have h0' : ∑ i, u i = α := by rw [h0]; ring
  have h1' : ∑ i, u i * x i = β := by rw [h1]; ring
  have h2' : ∑ i, u i * x i ^ 2 = -(h ^ 2 + w) / h * α := by
    rw [h2]; simp [Matrix.vecHead, Matrix.vecTail]; ring
  have h3' : ∑ i, u i * x i ^ 3 = -h * β := by
    have := hE 3
    simp only [e, o] at this
    rw [show ((3 : Fin 4) : ℕ) = 3 from rfl] at this
    rw [this]; simp [Matrix.vecHead, Matrix.vecTail]; try ring
  rw [h0', h1', h2', h3']
  have := Q_neg_plane hh hw α β hαβ
  linarith

end GppNoGo.QuartetFourNode
