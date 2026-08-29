import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Finite root escape for strict prime-gas Hankel positivity

A nonzero real polynomial of degree at most `N` cannot vanish on `N+1`
distinct support points.  This is the finite combinatorial input needed to
upgrade nonnegative weighted polynomial Gram forms to strict positivity once
the prime-gas measure supplies enough positive support points.
-/

namespace GppPrimeHankelRootEscape

open Polynomial

/-- If a finite real set contains more points than the natural degree of a
nonzero polynomial, at least one point is not a root. -/
theorem exists_eval_ne_zero_of_natDegree_lt_card
    (p : ℝ[X]) (S : Finset ℝ)
    (hp : p ≠ 0) (hcard : p.natDegree < S.card) :
    ∃ x ∈ S, p.eval x ≠ 0 := by
  by_contra h
  push_neg at h
  have hsubset : S.val ⊆ p.roots := by
    intro x hx
    rw [Polynomial.mem_roots hp]
    exact h x hx
  have hle : S.card ≤ p.natDegree :=
    Polynomial.card_le_degree_of_subset_roots hsubset
  omega

/-- Degree-bounded form: a nonzero polynomial of natural degree at most `N`
cannot vanish on a finite set of cardinality `N+1` or larger. -/
theorem exists_eval_ne_zero_of_card_gt_degree_bound
    (p : ℝ[X]) (S : Finset ℝ) (N : ℕ)
    (hp : p ≠ 0) (hdeg : p.natDegree ≤ N) (hcard : N < S.card) :
    ∃ x ∈ S, p.eval x ≠ 0 := by
  exact exists_eval_ne_zero_of_natDegree_lt_card p S hp (lt_of_le_of_lt hdeg hcard)

end GppPrimeHankelRootEscape

#print axioms GppPrimeHankelRootEscape.exists_eval_ne_zero_of_natDegree_lt_card
#print axioms GppPrimeHankelRootEscape.exists_eval_ne_zero_of_card_gt_degree_bound
