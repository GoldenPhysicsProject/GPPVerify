import GppVerify.RiemannHypothesis.PrimeHankelAllOrderStrict
import Mathlib.Tactic

/-!
# Strict two-parameter prime-gas Fisher quadratic form

The all-order strict arithmetic Hankel theorem immediately controls the two
sufficient statistics `log n` and `(log n)^2`.  This file packages that
specialization explicitly: every nonzero real coefficient pair gives a strictly
positive quadratic form against the von-Mangoldt Fisher weight on `β > 1`.
-/

namespace GppPrimeFisherTwoParameterStrict

open Polynomial BigOperators
open GppPrimeHankelAllOrderStrict
open GppPrimeHankelFisherSpecialization

/-- The degree-two score polynomial corresponding to the two sufficient
statistics `x` and `x^2`. -/
def scorePolynomial (a b : ℝ) : ℝ[X] :=
  C a * X + C b * X ^ 2

/-- Evaluation of the score polynomial is the expected linear combination
`a*x + b*x^2`. -/
theorem scorePolynomial_eval (a b x : ℝ) :
    (scorePolynomial a b).eval x = a * x + b * x ^ 2 := by
  simp [scorePolynomial]

/-- A nonzero coefficient pair gives a nonzero score polynomial. -/
theorem scorePolynomial_ne_zero {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) :
    scorePolynomial a b ≠ 0 := by
  intro hzero
  have h1 := congrArg (fun p : ℝ[X] => p.coeff 1) hzero
  have h2 := congrArg (fun p : ℝ[X] => p.coeff 2) hzero
  simp [scorePolynomial] at h1 h2
  exact hab.elim (fun ha => ha h1) (fun hb => hb h2)

/-- **Strict two-parameter prime-gas Fisher form.** For every `β > 1`, every
nonzero coefficient pair `(a,b)` has strictly positive squared score against
the actual von-Mangoldt Fisher measure. -/
theorem fisher_two_parameter_quadratic_pos
    {β a b : ℝ} (hβ : 1 < β) (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < ∑' n : ℕ,
      fisherWeight β n *
        (a * Real.log n + b * (Real.log n) ^ 2) ^ 2 := by
  have h := fisher_polynomial_tsum_pos_unconditional
    hβ (scorePolynomial a b) (scorePolynomial_ne_zero hab)
  simpa only [scorePolynomial_eval] using h

end GppPrimeFisherTwoParameterStrict

#print axioms GppPrimeFisherTwoParameterStrict.scorePolynomial_eval
#print axioms GppPrimeFisherTwoParameterStrict.scorePolynomial_ne_zero
#print axioms GppPrimeFisherTwoParameterStrict.fisher_two_parameter_quadratic_pos
