import GppVerify.RiemannHypothesis.PrimeFisherMomentSummability
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Polynomial-square summability for the prime-gas Hankel form

Once every weighted monomial `w n * x n ^ r` is summable, finite polynomial
induction upgrades this to `w n * p.eval (x n)`, and applying the result to `p^2`
gives the exact weighted-square summability needed by the infinite Gram theorem.
-/

namespace GppPrimeHankelPolynomialSummability

open Polynomial
open GppPrimeHankelFisherSpecialization
open GppPrimeFisherMomentSummability

/-- Finite polynomial evaluation preserves summability under summability of all weighted
monomials. -/
theorem summable_weight_mul_polynomial_eval
    (w x : ℕ → ℝ) (p : ℝ[X])
    (hpow : ∀ r : ℕ, Summable (fun n : ℕ => w n * (x n) ^ r)) :
    Summable (fun n : ℕ => w n * p.eval (x n)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have h := hp.add hq
      exact h.congr (fun n => by simp [mul_add])
  | monomial r a =>
      have h := (hpow r).mul_left a
      exact h.congr (fun n => by
        simp [mul_assoc, mul_left_comm, mul_comm])

/-- Applying the polynomial lemma to `p^2` gives summability of the weighted square. -/
theorem summable_weight_mul_polynomial_eval_sq
    (w x : ℕ → ℝ) (p : ℝ[X])
    (hpow : ∀ r : ℕ, Summable (fun n : ℕ => w n * (x n) ^ r)) :
    Summable (fun n : ℕ => w n * (p.eval (x n)) ^ 2) := by
  have h := summable_weight_mul_polynomial_eval w x (p ^ 2) hpow
  simpa using h

/-- For the actual prime-gas Fisher weight, polynomial-square summability holds for every
real polynomial on the honest half-plane `β > 1`. -/
theorem summable_fisherWeight_mul_polynomial_eval_sq
    {β : ℝ} (hβ : 1 < β) (p : ℝ[X]) :
    Summable
      (fun n : ℕ => fisherWeight β n * (p.eval (Real.log n)) ^ 2) := by
  apply summable_weight_mul_polynomial_eval_sq
  intro r
  exact summable_fisherWeight_mul_log_pow r hβ

end GppPrimeHankelPolynomialSummability

#print axioms GppPrimeHankelPolynomialSummability.summable_weight_mul_polynomial_eval
#print axioms GppPrimeHankelPolynomialSummability.summable_fisherWeight_mul_polynomial_eval_sq
