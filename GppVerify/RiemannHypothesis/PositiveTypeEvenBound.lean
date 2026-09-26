import GppVerify.RiemannHypothesis.HaarPositivityWeil
import Mathlib.Tactic

/-!
# Pointwise bound for even positive-type kernels

A real even positive-type kernel satisfies `|P(x)| <= P(0)`. This is the
2-by-2 principal-minor inequality, proved directly from the defining Gram form.
-/

namespace GppPositiveTypeEvenBound

open GppHaarPositivityWeil

/-- The upper half of the 2-by-2 positive-type bound. -/
theorem le_at_zero_of_even_positiveType {P : ℝ → ℝ}
    (hP : PositiveType P) (heven : ∀ x, P (-x) = P x) (x : ℝ) :
    P x ≤ P 0 := by
  have h := hP 2 ![0, x] ![(1 : ℂ), (-1 : ℂ)]
  simp [Fin.sum_univ_two, heven] at h
  linarith

/-- The lower half of the 2-by-2 positive-type bound. -/
theorem neg_at_zero_le_of_even_positiveType {P : ℝ → ℝ}
    (hP : PositiveType P) (heven : ∀ x, P (-x) = P x) (x : ℝ) :
    -P 0 ≤ P x := by
  have h := hP 2 ![0, x] ![(1 : ℂ), (1 : ℂ)]
  simp [Fin.sum_univ_two, heven] at h
  linarith

/-- Every value of an even real positive-type kernel is bounded in absolute
value by its value at the origin. -/
theorem abs_le_at_zero_of_even_positiveType {P : ℝ → ℝ}
    (hP : PositiveType P) (heven : ∀ x, P (-x) = P x) (x : ℝ) :
    |P x| ≤ P 0 := by
  rw [abs_le]
  exact ⟨neg_at_zero_le_of_even_positiveType hP heven x,
    le_at_zero_of_even_positiveType hP heven x⟩

end GppPositiveTypeEvenBound

#print axioms GppPositiveTypeEvenBound.abs_le_at_zero_of_even_positiveType
