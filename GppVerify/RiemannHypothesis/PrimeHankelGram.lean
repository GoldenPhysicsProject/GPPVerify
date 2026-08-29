import Mathlib.Tactic

open scoped BigOperators

namespace GppPrimeHankel

/--
Finite weighted polynomial Gram positivity. This is the algebraic core of the
prime-side Hankel moment hierarchy: any nonnegative discrete weight produces a
nonnegative quadratic form after evaluating a polynomial on the support.
-/
theorem finite_weighted_polynomial_gram_nonneg
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (N : ℕ) (c : Fin (N + 1) → ℝ) :
    0 ≤ ∑ i ∈ s, w i * (∑ j : Fin (N + 1), c j * (x i) ^ (j : ℕ)) ^ 2 := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i hi) (sq_nonneg _)

/-- The same positivity statement when the finite support is encoded directly
as a finite type rather than an explicit `Finset`. -/
theorem finite_type_weighted_polynomial_gram_nonneg
    {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (N : ℕ) (c : Fin (N + 1) → ℝ) :
    0 ≤ ∑ i : ι, w i * (∑ j : Fin (N + 1), c j * (x i) ^ (j : ℕ)) ^ 2 := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i) (sq_nonneg _)

/-- Two distinct support points with positive weights force the `2 × 2`
Hankel determinant to be strictly positive.  Algebraically the determinant is
exactly `w₁ w₂ (x₁-x₂)^2`; this is the strict core used when the prime-gas
measure supplies, for example, the distinct support points `log 2` and `log 3`. -/
theorem two_support_hankel_det_pos
    (w₁ w₂ x₁ x₂ : ℝ)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hx : x₁ ≠ x₂) :
    0 < (w₁ + w₂) * (w₁ * x₁ ^ 2 + w₂ * x₂ ^ 2) -
      (w₁ * x₁ + w₂ * x₂) ^ 2 := by
  have hdiff : 0 < (x₁ - x₂) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
  have hprod : 0 < w₁ * w₂ * (x₁ - x₂) ^ 2 := by positivity
  nlinarith [hprod]

/-- Exact determinant factorization behind `two_support_hankel_det_pos`. -/
theorem two_support_hankel_det_factor
    (w₁ w₂ x₁ x₂ : ℝ) :
    (w₁ + w₂) * (w₁ * x₁ ^ 2 + w₂ * x₂ ^ 2) -
      (w₁ * x₁ + w₂ * x₂) ^ 2 =
      w₁ * w₂ * (x₁ - x₂) ^ 2 := by
  ring

/-- Exact Cauchy--Binet/Vandermonde factorization for a `3 × 3` Hankel
moment matrix carried by exactly three weighted support points.  The left side
is `det [m_{i+j}]_{i,j=0}^2` expanded along the first row, with
`m_k = ∑_{a=1}^3 w_a x_a^k`. -/
theorem three_support_hankel_det_factor
    (w₁ w₂ w₃ x₁ x₂ x₃ : ℝ) :
    let m0 := w₁ + w₂ + w₃
    let m1 := w₁ * x₁ + w₂ * x₂ + w₃ * x₃
    let m2 := w₁ * x₁ ^ 2 + w₂ * x₂ ^ 2 + w₃ * x₃ ^ 2
    let m3 := w₁ * x₁ ^ 3 + w₂ * x₂ ^ 3 + w₃ * x₃ ^ 3
    let m4 := w₁ * x₁ ^ 4 + w₂ * x₂ ^ 4 + w₃ * x₃ ^ 4
    m0 * (m2 * m4 - m3 ^ 2) -
      m1 * (m1 * m4 - m2 * m3) +
      m2 * (m1 * m3 - m2 ^ 2) =
      w₁ * w₂ * w₃ *
        (x₁ - x₂) ^ 2 * (x₁ - x₃) ^ 2 * (x₂ - x₃) ^ 2 := by
  dsimp
  ring

/-- Three pairwise-distinct support points with positive weights force the
`3 × 3` Hankel determinant to be strictly positive.  This is the finite
algebraic core of the explicit prime witness at `log 2`, `log 3`, `log 5`. -/
theorem three_support_hankel_det_pos
    (w₁ w₂ w₃ x₁ x₂ x₃ : ℝ)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw₃ : 0 < w₃)
    (hx12 : x₁ ≠ x₂) (hx13 : x₁ ≠ x₃) (hx23 : x₂ ≠ x₃) :
    let m0 := w₁ + w₂ + w₃
    let m1 := w₁ * x₁ + w₂ * x₂ + w₃ * x₃
    let m2 := w₁ * x₁ ^ 2 + w₂ * x₂ ^ 2 + w₃ * x₃ ^ 2
    let m3 := w₁ * x₁ ^ 3 + w₂ * x₂ ^ 3 + w₃ * x₃ ^ 3
    let m4 := w₁ * x₁ ^ 4 + w₂ * x₂ ^ 4 + w₃ * x₃ ^ 4
    0 < m0 * (m2 * m4 - m3 ^ 2) -
      m1 * (m1 * m4 - m2 * m3) +
      m2 * (m1 * m3 - m2 ^ 2) := by
  dsimp
  rw [three_support_hankel_det_factor]
  have h12 : 0 < (x₁ - x₂) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx12)
  have h13 : 0 < (x₁ - x₃) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx13)
  have h23 : 0 < (x₂ - x₃) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx23)
  positivity

end GppPrimeHankel
