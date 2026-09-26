import GppVerify.RiemannHypothesis.FinitePrimePoissonSum
import GppVerify.RiemannHypothesis.PrimePoissonRadialPositiveType
import Mathlib.Tactic

/-!
# Finite-prime radial Poisson positivity

Each arbitrary-radial local prime response is positive type.  This file proves
that finite sums preserve positive type and applies that closure theorem to the
finite-prime response already identified with a finite Euler logarithmic-derivative sum.

No infinite prime limit or RH claim is made here.
-/

namespace GppFinitePrimePoissonPositiveType

open Complex Real
open GppHaarPositivityWeil
open GppPrimePoissonRadialPositiveType
open GppFinitePrimePoisson

/-- The zero function is positive type. -/
theorem positiveType_zero : PositiveType (fun _ : ℝ => 0) := by
  intro n x c
  simp

/-- Positive type is preserved under pointwise addition. -/
theorem positiveType_add {f g : ℝ → ℝ}
    (hf : PositiveType f) (hg : PositiveType g) :
    PositiveType (fun t => f t + g t) := by
  intro n x c
  have hf' := hf n x c
  have hg' := hg n x c
  have heq :
      (∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ (c i)) * c j * (((f (x i - x j) + g (x i - x j)) : ℝ) : ℂ)) =
      (∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ (c i)) * c j * (f (x i - x j) : ℂ)) +
      (∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ (c i)) * c j * (g (x i - x j) : ℂ)) := by
    push_cast
    simp_rw [mul_add, Finset.sum_add_distrib]
  rw [heq, Complex.add_re]
  exact add_nonneg hf' hg'

/-- Any finite pointwise sum of positive-type functions is positive type. -/
theorem positiveType_finset_sum
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ S, PositiveType (f i)) :
    PositiveType (fun t => ∑ i in S, f i t) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using positiveType_zero
  | @insert a S ha ih =>
      have haPT : PositiveType (f a) := hf a (by simp)
      have hSPT : PositiveType (fun t => ∑ i in S, f i t) := by
        apply ih
        intro i hi
        exact hf i (by simp [hi])
      simpa [ha] using positiveType_add haPT hSPT

/-- **Finite-prime radial positivity.**  For any finite set of integers all greater than one,
its Poisson/Euler response is positive type at every radial parameter `a>0`. -/
theorem finitePrimePoissonResponse_positiveType
    (S : Finset ℕ) (hS : ∀ p ∈ S, 1 < p) {a : ℝ} (ha : 0 < a) :
    PositiveType (finitePrimePoissonResponse S a) := by
  unfold finitePrimePoissonResponse
  apply positiveType_finset_sum
  intro p hp
  exact WpA_positiveType (by exact_mod_cast hS p hp) ha

end GppFinitePrimePoissonPositiveType

#print axioms GppFinitePrimePoissonPositiveType.positiveType_zero
#print axioms GppFinitePrimePoissonPositiveType.positiveType_add
#print axioms GppFinitePrimePoissonPositiveType.positiveType_finset_sum
#print axioms GppFinitePrimePoissonPositiveType.finitePrimePoissonResponse_positiveType
