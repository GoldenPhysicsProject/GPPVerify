import GppVerify.RiemannHypothesis.PrimePoissonRadialPositiveType
import Mathlib.Tactic

/-!
# Cosine kernels are positive type

This gives the finite-atomic Fourier kernel needed for von Mangoldt truncations.
For complex coefficients, the cosine Gram form is the sum of the squared norms
of its cosine and sine feature maps.
-/

namespace GppCosinePositiveType

open Complex Real
open GppHaarPositivityWeil
open GppPrimePoissonRadialPositiveType

/-- The basic real cosine kernel is positive type. -/
theorem cos_positiveType : PositiveType Real.cos := by
  intro N x c
  let A : ℂ := ∑ j : Fin N, c j * (Real.cos (x j) : ℂ)
  let B : ℂ := ∑ j : Fin N, c j * (Real.sin (x j) : ℂ)
  have hfactor : ∀ j k : Fin N,
      (starRingEnd ℂ (c j)) * c k * (Real.cos (x j - x k) : ℂ) =
        ((starRingEnd ℂ (c j)) * (Real.cos (x j) : ℂ)) *
          (c k * (Real.cos (x k) : ℂ)) +
        ((starRingEnd ℂ (c j)) * (Real.sin (x j) : ℂ)) *
          (c k * (Real.sin (x k) : ℂ)) := by
    intro j k
    rw [Real.cos_sub]
    push_cast
    ring
  have hconjA :
      (∑ j : Fin N, (starRingEnd ℂ (c j)) * (Real.cos (x j) : ℂ)) =
        (starRingEnd ℂ) A := by
    dsimp [A]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul]
    simp
  have hconjB :
      (∑ j : Fin N, (starRingEnd ℂ (c j)) * (Real.sin (x j) : ℂ)) =
        (starRingEnd ℂ) B := by
    dsimp [B]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul]
    simp
  have heq :
      (∑ j : Fin N, ∑ k : Fin N,
        (starRingEnd ℂ (c j)) * c k * (Real.cos (x j - x k) : ℂ)) =
      ((Complex.normSq A + Complex.normSq B : ℝ) : ℂ) := by
    simp_rw [hfactor, Finset.sum_add_distrib]
    rw [← Fintype.sum_mul_sum, ← Fintype.sum_mul_sum]
    rw [hconjA, hconjB]
    rw [mul_comm ((starRingEnd ℂ) A) A, Complex.mul_conj]
    rw [mul_comm ((starRingEnd ℂ) B) B, Complex.mul_conj]
    push_cast
    ring
  rw [heq, Complex.ofReal_re]
  exact add_nonneg (Complex.normSq_nonneg A) (Complex.normSq_nonneg B)

/-- Any real-frequency cosine kernel is positive type. -/
theorem cos_mul_positiveType (ω : ℝ) :
    PositiveType (fun t => Real.cos (ω * t)) := by
  exact positiveType_comp_mul cos_positiveType ω

/-- A nonnegative weighted cosine kernel is positive type. -/
theorem nonneg_mul_cos_positiveType {w : ℝ} (hw : 0 ≤ w) (ω : ℝ) :
    PositiveType (fun t => w * Real.cos (ω * t)) := by
  exact positiveType_nonneg_mul (cos_mul_positiveType ω) hw

end GppCosinePositiveType

#print axioms GppCosinePositiveType.cos_positiveType
#print axioms GppCosinePositiveType.cos_mul_positiveType
#print axioms GppCosinePositiveType.nonneg_mul_cos_positiveType
