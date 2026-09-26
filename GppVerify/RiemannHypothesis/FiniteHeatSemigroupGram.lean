import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Finite positive heat-semigroup Gram core

This file isolates the finite algebra behind the August arithmetic heat criterion.
If a heat kernel is a finite positive atomic Laplace sum

  K(t) = Σ_a w_a exp(-λ_a t),    w_a ≥ 0,

then the additive-semigroup matrix `G_ij = K(t_i+t_j)` is positive semidefinite.
Indeed it is a sum of weighted rank-one Gram matrices.

This is a one-way finite spectral theorem only.  It does NOT assert that the explicit
prime--Archimedean arithmetic heat function has such a representation, and therefore
makes no RH claim.
-/

namespace GppFiniteHeatSemigroupGram

open Real
open scoped BigOperators

/-- Finite positive atomic heat trace. -/
noncomputable def atomicHeat
    {α : Type*} (atoms : Finset α) (weight rate : α → ℝ) (t : ℝ) : ℝ :=
  ∑ a in atoms, weight a * Real.exp (-(rate a) * t)

/-- Two-time finite heat kernel written in rank-one form. -/
noncomputable def atomicHeatKernel
    {α : Type*} (atoms : Finset α) (weight rate : α → ℝ) (t u : ℝ) : ℝ :=
  ∑ a in atoms,
    weight a * Real.exp (-(rate a) * t) * Real.exp (-(rate a) * u)

/-- The rank-one kernel is exactly the additive heat-semigroup kernel `K(t+u)`. -/
theorem atomicHeatKernel_eq_atomicHeat_add
    {α : Type*} [DecidableEq α]
    (atoms : Finset α) (weight rate : α → ℝ) (t u : ℝ) :
    atomicHeatKernel atoms weight rate t u = atomicHeat atoms weight rate (t + u) := by
  unfold atomicHeatKernel atomicHeat
  apply Finset.sum_congr rfl
  intro a ha
  calc
    weight a * Real.exp (-(rate a) * t) * Real.exp (-(rate a) * u) =
        weight a *
          (Real.exp (-(rate a) * t) * Real.exp (-(rate a) * u)) := by ring
    _ = weight a * Real.exp (-(rate a) * t + (-(rate a) * u)) := by
      rw [Real.exp_add]
    _ = weight a * Real.exp (-(rate a) * (t + u)) := by
      congr 2
      ring

/-- Weighted rank-one quadratic forms are nonnegative. -/
theorem weighted_rankOne_sum_nonneg
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (atoms : Finset α) (I : Finset ι)
    (weight rate : α → ℝ) (coeff time : ι → ℝ)
    (hweight : ∀ a ∈ atoms, 0 ≤ weight a) :
    0 ≤ ∑ a in atoms,
      weight a * (∑ i in I, coeff i * Real.exp (-(rate a) * time i)) ^ 2 := by
  exact Finset.sum_nonneg fun a ha =>
    mul_nonneg (hweight a ha) (sq_nonneg _)

/-- **Finite heat Gram positivity.**  Every finite positive atomic heat spectrum gives
an additive-semigroup positive kernel. -/
theorem atomicHeatKernel_gram_nonneg
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (atoms : Finset α) (I : Finset ι)
    (weight rate : α → ℝ) (coeff time : ι → ℝ)
    (hweight : ∀ a ∈ atoms, 0 ≤ weight a) :
    0 ≤ ∑ i in I, ∑ j in I,
      coeff i * coeff j * atomicHeatKernel atoms weight rate (time i) (time j) := by
  have hsq := weighted_rankOne_sum_nonneg atoms I weight rate coeff time hweight
  suffices hident :
      (∑ i in I, ∑ j in I,
        coeff i * coeff j * atomicHeatKernel atoms weight rate (time i) (time j)) =
      ∑ a in atoms,
        weight a * (∑ i in I, coeff i * Real.exp (-(rate a) * time i)) ^ 2 by
    rw [hident]
    exact hsq
  unfold atomicHeatKernel
  simp_rw [Finset.mul_sum]
  calc
    (∑ i in I, ∑ j in I, ∑ a in atoms,
      coeff i * coeff j *
        (weight a * Real.exp (-(rate a) * time i) *
          Real.exp (-(rate a) * time j))) =
      ∑ i in I, ∑ a in atoms, ∑ j in I,
        coeff i * coeff j *
          (weight a * Real.exp (-(rate a) * time i) *
            Real.exp (-(rate a) * time j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ a in atoms, ∑ i in I, ∑ j in I,
        coeff i * coeff j *
          (weight a * Real.exp (-(rate a) * time i) *
            Real.exp (-(rate a) * time j)) := by
      rw [Finset.sum_comm]
    _ = ∑ a in atoms,
        weight a * (∑ i in I, coeff i * Real.exp (-(rate a) * time i)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      symm
      calc
        weight a * (∑ i in I, coeff i * Real.exp (-(rate a) * time i)) ^ 2 =
            weight a *
              ((∑ i in I, coeff i * Real.exp (-(rate a) * time i)) *
               (∑ j in I, coeff j * Real.exp (-(rate a) * time j))) := by
          rw [pow_two]
        _ = weight a *
              (∑ i in I, ∑ j in I,
                (coeff i * Real.exp (-(rate a) * time i)) *
                  (coeff j * Real.exp (-(rate a) * time j))) := by
          congr 1
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
        _ = ∑ i in I, ∑ j in I,
              weight a *
                ((coeff i * Real.exp (-(rate a) * time i)) *
                  (coeff j * Real.exp (-(rate a) * time j))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
        _ = ∑ i in I, ∑ j in I,
              coeff i * coeff j *
                (weight a * Real.exp (-(rate a) * time i) *
                  Real.exp (-(rate a) * time j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring

/-- Equivalent `K(t_i+t_j)` form of the same finite Gram positivity theorem. -/
theorem atomicHeat_add_gram_nonneg
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (atoms : Finset α) (I : Finset ι)
    (weight rate : α → ℝ) (coeff time : ι → ℝ)
    (hweight : ∀ a ∈ atoms, 0 ≤ weight a) :
    0 ≤ ∑ i in I, ∑ j in I,
      coeff i * coeff j * atomicHeat atoms weight rate (time i + time j) := by
  simpa [atomicHeatKernel_eq_atomicHeat_add] using
    atomicHeatKernel_gram_nonneg atoms I weight rate coeff time hweight

end GppFiniteHeatSemigroupGram

#print axioms GppFiniteHeatSemigroupGram.atomicHeatKernel_eq_atomicHeat_add
#print axioms GppFiniteHeatSemigroupGram.atomicHeatKernel_gram_nonneg
#print axioms GppFiniteHeatSemigroupGram.atomicHeat_add_gram_nonneg
