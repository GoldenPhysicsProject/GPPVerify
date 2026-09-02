import Mathlib.Tactic

/-!
# Finite raw-moment factorization

A bookkeeping lemma for the arbitrary finite-support Fisher/Vandermonde identity.
It factors an ordered triple sum of separable monomials into the product of the
corresponding raw moments.
-/

open scoped BigOperators

namespace GppFiniteMomentFactorization

/-- Raw moment of order `r` for a finite weighted support. -/
def rawMoment {n : ℕ} (p x : Fin n → ℝ) (r : ℕ) : ℝ :=
  ∑ i : Fin n, p i * x i ^ r

/-- Every separable ordered triple monomial factors into three raw moments. -/
theorem triple_monomial_factorization
    {n : ℕ} (p x : Fin n → ℝ) (a b c : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (p i * x i ^ a) * (p j * x j ^ b) * (p k * x k ^ c)) =
      rawMoment p x a * rawMoment p x b * rawMoment p x c := by
  unfold rawMoment
  calc
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (p i * x i ^ a) * (p j * x j ^ b) * (p k * x k ^ c)) =
      ∑ i : Fin n, ∑ j : Fin n,
        ((p i * x i ^ a) * (p j * x j ^ b)) *
          (∑ k : Fin n, p k * x k ^ c) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
    _ = ∑ i : Fin n,
        ((p i * x i ^ a) * (∑ j : Fin n, p j * x j ^ b)) *
          (∑ k : Fin n, p k * x k ^ c) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = (∑ i : Fin n, p i * x i ^ a) *
          (∑ j : Fin n, p j * x j ^ b) *
          (∑ k : Fin n, p k * x k ^ c) := by
            rw [← Finset.sum_mul, ← Finset.sum_mul]

/-- Scalar-aware version of `triple_monomial_factorization`.  Keeping the
coefficient outside the separable monomial is useful after expanding a
Vandermonde square: integer coefficients such as `2` and `6` can be pulled
through the three finite sums without asking simp to reorder binders. -/
theorem triple_monomial_factorization_smul
    {n : ℕ} (p x : Fin n → ℝ) (r : ℝ) (a b c : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      r * ((p i * x i ^ a) * (p j * x j ^ b) * (p k * x k ^ c))) =
      r * (rawMoment p x a * rawMoment p x b * rawMoment p x c) := by
  calc
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      r * ((p i * x i ^ a) * (p j * x j ^ b) * (p k * x k ^ c))) =
      r * (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (p i * x i ^ a) * (p j * x j ^ b) * (p k * x k ^ c)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
    _ = r * (rawMoment p x a * rawMoment p x b * rawMoment p x c) := by
      rw [triple_monomial_factorization]

end GppFiniteMomentFactorization

#print axioms GppFiniteMomentFactorization.triple_monomial_factorization
#print axioms GppFiniteMomentFactorization.triple_monomial_factorization_smul
