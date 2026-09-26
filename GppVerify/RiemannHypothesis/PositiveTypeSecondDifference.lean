import GppVerify.RiemannHypothesis.HaarPositivityWeil
import Mathlib.Tactic

/-!
# Three-point second-difference inequality for even positive-type kernels

Testing a real even positive-type kernel on the three points `0,t,2t` with
coefficients `(1,-2,1)` gives

  `3 P(0) - 4 P(t) + P(2t) >= 0`.

This is a genuinely stronger finite-Gram consequence than the two-point bound
`|P(t)| <= P(0)`.
-/

namespace GppPositiveTypeSecondDifference

open GppHaarPositivityWeil

/-- Three-point positive-type inequality at equally spaced points. -/
theorem second_difference_lower_bound {P : ℝ → ℝ}
    (hP : PositiveType P) (heven : ∀ x, P (-x) = P x) (t : ℝ) :
    0 ≤ 3 * P 0 - 4 * P t + P (2 * t) := by
  have h := hP 3 ![0, t, 2 * t] ![(1 : ℂ), (-2 : ℂ), (1 : ℂ)]
  simp [Fin.sum_univ_succ, heven] at h
  linarith

/-- Rearranged form: `P(2t) >= 4P(t)-3P(0)`. -/
theorem four_mul_le {P : ℝ → ℝ}
    (hP : PositiveType P) (heven : ∀ x, P (-x) = P x) (t : ℝ) :
    4 * P t - 3 * P 0 ≤ P (2 * t) := by
  linarith [second_difference_lower_bound hP heven t]

end GppPositiveTypeSecondDifference

#print axioms GppPositiveTypeSecondDifference.second_difference_lower_bound
