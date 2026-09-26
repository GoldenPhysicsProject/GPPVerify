import Mathlib

/-!
# Euler logarithm and the causal prime-power anomaly

For a prime-local logarithm

  -log(1 - p^(-1/2) V) = sum_{m>=1} p^(-m/2) V^m / m,

the `m` in the translation length `m log p` cancels the Euler-logarithm
coefficient `1/m`.  Therefore the trace anomaly of the `m`-th repeated orbit
carries the exact von Mangoldt weight `log p`, not `m log p`.

This file formalizes that exact algebraic cancellation and its finite-sum form.
It does not formalize the Dirichlet heat commutator trace-class theorem itself.
-/

namespace GppArithmeticEulerLogAnomaly

open scoped BigOperators

/-- The Euler logarithm coefficient `1/m` cancels the repetition multiplicity
in the orbit length `m log p`. -/
theorem repetition_cancel (p : ℝ) (m : ℕ) (hm : 0 < m) :
    (1 / (m : ℝ)) * ((m : ℝ) * Real.log p) = Real.log p := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp

/-- Gaussian heat factor associated to a logarithmic orbit length. -/
noncomputable def gaussianLength (t a : ℝ) : ℝ :=
  Real.exp (-(a^2) / (4 * t))

/-- The `m`-th term before cancelling the Euler-logarithm repetition factor. -/
noncomputable def repeatedPrimeTerm (p t : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-((m : ℝ) / 2) * Real.log p) *
    ((1 / (m : ℝ)) * ((m : ℝ) * Real.log p)) *
    gaussianLength t ((m : ℝ) * Real.log p)

/-- The same term in exact von-Mangoldt form. -/
noncomputable def vonMangoldtPrimePowerTerm (p t : ℝ) (m : ℕ) : ℝ :=
  Real.log p *
    Real.exp (-((m : ℝ) / 2) * Real.log p) *
    gaussianLength t ((m : ℝ) * Real.log p)

/-- Every nonzero repetition term is exactly the prime-power von Mangoldt term. -/
theorem repeatedPrimeTerm_eq_vonMangoldt
    (p t : ℝ) (m : ℕ) (hm : 0 < m) :
    repeatedPrimeTerm p t m = vonMangoldtPrimePowerTerm p t m := by
  unfold repeatedPrimeTerm vonMangoldtPrimePowerTerm
  rw [repetition_cancel p m hm]
  ring

/-- Hence every finite Euler-logarithm truncation equals the corresponding
finite sum with exact `log p` coefficients. -/
theorem truncated_eulerLog_eq_vonMangoldt
    (p t : ℝ) (M : ℕ) :
    (∑ m ∈ Finset.range M,
      repeatedPrimeTerm p t (m + 1)) =
    ∑ m ∈ Finset.range M,
      vonMangoldtPrimePowerTerm p t (m + 1) := by
  apply Finset.sum_congr rfl
  intro m hm
  exact repeatedPrimeTerm_eq_vonMangoldt p t (m + 1) (Nat.succ_pos m)

end GppArithmeticEulerLogAnomaly

#print axioms GppArithmeticEulerLogAnomaly.repetition_cancel
#print axioms GppArithmeticEulerLogAnomaly.repeatedPrimeTerm_eq_vonMangoldt
#print axioms GppArithmeticEulerLogAnomaly.truncated_eulerLog_eq_vonMangoldt
