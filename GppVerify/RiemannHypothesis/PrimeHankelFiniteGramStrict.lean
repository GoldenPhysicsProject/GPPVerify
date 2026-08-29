import GppVerify.RiemannHypothesis.PrimeHankelRootEscape
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Strict finite weighted polynomial Gram positivity

This file packages the root-escape theorem into the exact positivity statement
needed for finite truncations of the prime-gas Hankel quadratic form.
-/

namespace GppPrimeHankelFiniteGramStrict

open Polynomial BigOperators
open GppPrimeHankelRootEscape

/-- A positive weighted polynomial Gram sum is strictly positive once the support
contains more points than the degree bound of a nonzero polynomial. -/
theorem weighted_eval_sq_sum_pos
    (p : ℝ[X]) (S : Finset ℝ) (w : ℝ → ℝ) (N : ℕ)
    (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ N)
    (hcard : N < S.card)
    (hw : ∀ x ∈ S, 0 < w x) :
    0 < ∑ x ∈ S, w x * (p.eval x) ^ 2 := by
  rcases exists_eval_ne_zero_of_card_gt_degree_bound p S N hp hdeg hcard with
    ⟨x, hx, hpx⟩
  apply Finset.sum_pos'
  · intro y hy
    exact mul_nonneg (hw y hy).le (sq_nonneg (p.eval y))
  · refine ⟨x, hx, ?_⟩
    exact mul_pos (hw x hx) (sq_pos_of_ne_zero hpx)

end GppPrimeHankelFiniteGramStrict

#print axioms GppPrimeHankelFiniteGramStrict.weighted_eval_sq_sum_pos
