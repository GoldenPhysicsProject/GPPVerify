import Mathlib

/-!
# Arithmetic defect positivity

This file isolates the abstract contraction mechanism behind the proposed
prime--Archimedean box factorization.  If a signed arithmetic box quantity can
be represented as an ambient positive norm square minus the norm square of a
contractive ghost/prime channel, then the box quantity is nonnegative.

This is only the abstract Hilbert-space inequality.  It does not construct the
arithmetic contraction or identify its defect with Suzuki's screw function.
-/

namespace GppArithmeticDefectPositivity

/-- A contraction inequality implies nonnegativity of the corresponding norm-square defect. -/
theorem normSq_sub_normSq_nonneg
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (x : E) (y : F) (h : ‖y‖ ≤ ‖x‖) :
    0 ≤ ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  nlinarith

/-- If an arithmetic quantity is exactly a contractive norm-square defect,
then it is nonnegative. -/
theorem defect_representation_nonneg
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (x : E) (y : F) (Ψ : ℝ)
    (hcontract : ‖y‖ ≤ ‖x‖)
    (hrep : Ψ = ‖x‖ ^ 2 - ‖y‖ ^ 2) :
    0 ≤ Ψ := by
  rw [hrep]
  exact normSq_sub_normSq_nonneg x y hcontract

/-- The stronger exact-square case used by a quotient/GNS realization. -/
theorem square_representation_nonneg
    {E : Type*} [NormedAddCommGroup E]
    (x : E) (Ψ : ℝ) (hrep : Ψ = ‖x‖ ^ 2) :
    0 ≤ Ψ := by
  rw [hrep]
  exact sq_nonneg ‖x‖

end GppArithmeticDefectPositivity

#print axioms GppArithmeticDefectPositivity.normSq_sub_normSq_nonneg
#print axioms GppArithmeticDefectPositivity.defect_representation_nonneg
#print axioms GppArithmeticDefectPositivity.square_representation_nonneg
