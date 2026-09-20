import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

/-!
# Reflection-positive graph = contraction

This file isolates the finite scalar core of the two-copy BPY/OS construction.

For a graph vector (z,c z) in a two-copy Hilbert carrier with fundamental symmetry

    J = diag(+1,-1),

the J-quadratic form is

    |z|^2 - |c z|^2.

It is nonnegative for every z exactly when |c|<=1.

The infinite-dimensional Hilbert-space statement is the same identity with a bounded
operator C in place of the scalar c:

    <(x,Cx),J(x,Cx)> = ||x||^2 - ||Cx||^2.

Thus the RH reflection-positivity target in the two-copy colligation is precisely a
contractivity theorem for the odd/even graph transfer.
-/

namespace GppReflectionPositiveGraph

open Complex

/-- Scalar two-copy J-form on the graph of multiplication by c. -/
def graphJForm (c z : ℂ) : ℝ :=
  Complex.normSq z - Complex.normSq (c*z)

/-- Exact factorization of the graph J-form. -/
theorem graphJForm_factor (c z : ℂ) :
    graphJForm c z =
      Complex.normSq z * (1 - Complex.normSq c) := by
  simp [graphJForm, Complex.normSq_apply]
  ring

/-- Contractivity implies reflection positivity of every graph vector. -/
theorem graph_nonneg_of_norm_le_one
    (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ∀ z : ℂ, 0 ≤ graphJForm c z := by
  intro z
  rw [graphJForm_factor]
  apply mul_nonneg
  · exact Complex.normSq_nonneg z
  · have hsq : Complex.normSq c ≤ 1 := by
      rw [Complex.sq_norm]
      nlinarith [norm_nonneg c]
    linarith

/-- Reflection positivity of all graph vectors forces contractivity. -/
theorem norm_le_one_of_graph_nonneg
    (c : ℂ) (hpos : ∀ z : ℂ, 0 ≤ graphJForm c z) :
    ‖c‖ ≤ 1 := by
  have h1 := hpos 1
  rw [graphJForm_factor] at h1
  norm_num [Complex.normSq_apply] at h1
  rw [← Complex.sq_norm] at h1
  nlinarith [norm_nonneg c]

/--
Capstone: positivity of the two-copy graph in the fundamental symmetry is equivalent
to contractivity of the transfer scalar.
-/
theorem graph_nonnegative_iff_contractive (c : ℂ) :
    (∀ z : ℂ, 0 ≤ graphJForm c z) ↔ ‖c‖ ≤ 1 := by
  constructor
  · exact norm_le_one_of_graph_nonneg c
  · exact graph_nonneg_of_norm_le_one c

/-- Strict expansion produces an explicit negative graph direction, already at z=1. -/
theorem negative_witness_of_one_lt_norm
    (c : ℂ) (hc : 1 < ‖c‖) :
    graphJForm c 1 < 0 := by
  rw [graphJForm_factor]
  norm_num [Complex.normSq_apply]
  rw [← Complex.sq_norm]
  nlinarith [norm_nonneg c]

end GppReflectionPositiveGraph


/-! ## Abstract normed-space graph theorem -/

section AbstractGraph

variable {H K : Type*} [SeminormedAddCommGroup H] [SeminormedAddCommGroup K]

/-- The abstract fundamental-symmetry graph form, written in norm coordinates. -/
def abstractGraphJForm (C : H → K) (x : H) : ℝ :=
  ‖x‖^2 - ‖C x‖^2

/--
For any map between seminormed additive groups, nonnegativity of the graph J-form is
exactly pointwise contractivity.  Linearity is not needed for this equivalence.
-/
theorem abstract_graph_nonnegative_iff_contractive (C : H → K) :
    (∀ x : H, 0 ≤ abstractGraphJForm C x) ↔
      (∀ x : H, ‖C x‖ ≤ ‖x‖) := by
  constructor
  · intro h x
    have hx := h x
    have hnx : 0 ≤ ‖x‖ := norm_nonneg x
    have hnc : 0 ≤ ‖C x‖ := norm_nonneg (C x)
    dsimp [abstractGraphJForm] at hx
    nlinarith
  · intro h x
    have hc := h x
    have hnx : 0 ≤ ‖x‖ := norm_nonneg x
    have hnc : 0 ≤ ‖C x‖ := norm_nonneg (C x)
    dsimp [abstractGraphJForm]
    nlinarith

/-- Failure of contractivity is exactly an explicit negative graph direction. -/
theorem abstract_negative_graph_witness_iff
    (C : H → K) :
    (∃ x : H, abstractGraphJForm C x < 0) ↔
      (∃ x : H, ‖x‖ < ‖C x‖) := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨x,?_⟩
    have hnx : 0 ≤ ‖x‖ := norm_nonneg x
    have hnc : 0 ≤ ‖C x‖ := norm_nonneg (C x)
    dsimp [abstractGraphJForm] at hx
    nlinarith
  · rintro ⟨x,hx⟩
    refine ⟨x,?_⟩
    have hnx : 0 ≤ ‖x‖ := norm_nonneg x
    have hnc : 0 ≤ ‖C x‖ := norm_nonneg (C x)
    dsimp [abstractGraphJForm]
    nlinarith

end AbstractGraph

#print axioms GppReflectionPositiveGraph.graphJForm_factor
#print axioms GppReflectionPositiveGraph.abstract_graph_nonnegative_iff_contractive
#print axioms GppReflectionPositiveGraph.abstract_negative_graph_witness_iff
#print axioms GppReflectionPositiveGraph.graph_nonnegative_iff_contractive
#print axioms GppReflectionPositiveGraph.negative_witness_of_one_lt_norm
