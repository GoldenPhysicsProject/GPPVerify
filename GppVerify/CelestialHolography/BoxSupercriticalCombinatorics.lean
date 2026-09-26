import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Combinatorial core of the supercritical massless-box hierarchy

Expanding the m-th power of the massless box Symanzik polynomial produces
Dirichlet-moment coefficients

  choose m j * (j!)^2 * ((m-j)!)^2.

For j<=m this collapses exactly to

  m! * j! * (m-j)!,

which is the algebraic step behind the Discovery2 all-order formula

  integral_{Delta_3} F^m
    = m!/(2m+3)! * sum_j j!(m-j)! s^j t^(m-j).

This file proves only that exact combinatorial collapse.  It does not assume or
formalize the multivariate simplex integral.
-/

namespace GppBoxSupercriticalCombinatorics

/-- Exact factorial collapse of each binomial/Dirichlet coefficient. -/
theorem choose_factorial_square_collapse {m j : ℕ} (hj : j ≤ m) :
    Nat.choose m j * (j !) ^ 2 * ((m - j) !) ^ 2 =
      m ! * j ! * (m - j) ! := by
  have h := Nat.choose_mul_factorial_mul_factorial hj
  calc
    Nat.choose m j * (j !) ^ 2 * ((m - j) !) ^ 2
        = (Nat.choose m j * j ! * (m - j) !) * (j ! * (m - j) !) := by ring
    _ = m ! * (j ! * (m - j) !) := by rw [h]
    _ = m ! * j ! * (m - j) ! := by ring

/-- The same identity after coercion to the reals, matching the coefficient ring
used in the Feynman-parameter polynomial. -/
theorem choose_factorial_square_collapse_real {m j : ℕ} (hj : j ≤ m) :
    (Nat.choose m j : ℝ) * (j ! : ℝ) ^ 2 * ((m - j) ! : ℝ) ^ 2 =
      (m ! : ℝ) * (j ! : ℝ) * ((m - j) ! : ℝ) := by
  exact_mod_cast choose_factorial_square_collapse hj

end GppBoxSupercriticalCombinatorics

#print axioms GppBoxSupercriticalCombinatorics.choose_factorial_square_collapse
#print axioms GppBoxSupercriticalCombinatorics.choose_factorial_square_collapse_real
