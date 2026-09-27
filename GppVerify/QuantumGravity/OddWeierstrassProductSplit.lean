import Mathlib.Tactic

/-!
# Finite odd/even split for Weierstrass products

This module isolates the finite combinatorial factorization needed to pass from
the full `sinh` Weierstrass product to its odd subproduct.  It deliberately
proves only exact finite identities; no infinite-product limit or logarithmic
differentiation is asserted here.
-/

namespace GppOddWeierstrassProductSplit

open scoped BigOperators

/-- Splitting a product over `0, ..., 2N-1` into its even and odd indices. -/
theorem prod_range_even_mul_odd (f : ℕ → ℝ) : ∀ N : ℕ,
    (∏ k ∈ Finset.range N, f (2 * k)) *
        (∏ k ∈ Finset.range N, f (2 * k + 1)) =
      ∏ j ∈ Finset.range (2 * N), f j := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega]
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      rw [← ih]
      ring

/-- An even denominator in the full Weierstrass product is exactly a rescaled
    denominator in the half-argument product. -/
theorem weierstrass_even_factor_rescale (x : ℝ) (k : ℕ) :
    (1 : ℝ) + x ^ 2 / (((2 * k + 2 : ℕ) : ℝ) ^ 2) =
      1 + (x / 2) ^ 2 / (((k + 1 : ℕ) : ℝ) ^ 2) := by
  have hk : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hcast : (((2 * k + 2 : ℕ) : ℝ)) = 2 * (((k + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  rw [hcast]
  field_simp [hk]

/-- The product over the even positive denominators `2,4,...,2N` is exactly
    the ordinary Weierstrass product at half the argument. -/
theorem prod_weierstrass_even_rescale (x : ℝ) (N : ℕ) :
    (∏ k ∈ Finset.range N,
        ((1 : ℝ) + x ^ 2 / (((2 * k + 2 : ℕ) : ℝ) ^ 2))) =
      ∏ k ∈ Finset.range N,
        ((1 : ℝ) + (x / 2) ^ 2 / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
  apply Finset.prod_congr rfl
  intro k hk
  exact weierstrass_even_factor_rescale x k

/-- The positive-denominator Weierstrass product through `2N` factors exactly
    into its odd and even positive-denominator subproducts. -/
theorem prod_weierstrass_odd_mul_even (x : ℝ) (N : ℕ) :
    (∏ k ∈ Finset.range N,
        ((1 : ℝ) + x ^ 2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2))) *
      (∏ k ∈ Finset.range N,
        ((1 : ℝ) + x ^ 2 / (((2 * k + 2 : ℕ) : ℝ) ^ 2))) =
      ∏ j ∈ Finset.range (2 * N),
        ((1 : ℝ) + x ^ 2 / (((j + 1 : ℕ) : ℝ) ^ 2)) := by
  simpa [Nat.add_assoc] using
    (prod_range_even_mul_odd
      (fun j : ℕ => (1 : ℝ) + x ^ 2 / (((j + 1 : ℕ) : ℝ) ^ 2)) N)

/-- Exact finite quotient precursor: the odd positive-denominator product times
    the ordinary half-argument product equals the full product through `2N`. -/
theorem prod_weierstrass_odd_mul_half_eq_full (x : ℝ) (N : ℕ) :
    (∏ k ∈ Finset.range N,
        ((1 : ℝ) + x ^ 2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2))) *
      (∏ k ∈ Finset.range N,
        ((1 : ℝ) + (x / 2) ^ 2 / (((k + 1 : ℕ) : ℝ) ^ 2))) =
      ∏ j ∈ Finset.range (2 * N),
        ((1 : ℝ) + x ^ 2 / (((j + 1 : ℕ) : ℝ) ^ 2)) := by
  rw [← prod_weierstrass_even_rescale x N]
  exact prod_weierstrass_odd_mul_even x N

/-- Every finite half-argument Weierstrass product is strictly positive. -/
theorem prod_weierstrass_half_pos (x : ℝ) (N : ℕ) :
    0 < ∏ k ∈ Finset.range N,
      ((1 : ℝ) + (x / 2) ^ 2 / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
  apply Finset.prod_pos
  intro k hk
  have hden : 0 < (((k + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hterm : 0 ≤ (x / 2) ^ 2 / (((k + 1 : ℕ) : ℝ) ^ 2) :=
    div_nonneg (sq_nonneg (x / 2)) (le_of_lt hden)
  linarith

/-- Literal finite quotient identity for the odd Weierstrass subproduct. -/
theorem prod_weierstrass_odd_eq_full_div_half (x : ℝ) (N : ℕ) :
    (∏ k ∈ Finset.range N,
        ((1 : ℝ) + x ^ 2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2))) =
      ((∏ j ∈ Finset.range (2 * N),
          ((1 : ℝ) + x ^ 2 / (((j + 1 : ℕ) : ℝ) ^ 2))) /
        ∏ k ∈ Finset.range N,
          ((1 : ℝ) + (x / 2) ^ 2 / (((k + 1 : ℕ) : ℝ) ^ 2))) := by
  have hpos := prod_weierstrass_half_pos x N
  have hne : (∏ k ∈ Finset.range N,
      ((1 : ℝ) + (x / 2) ^ 2 / (((k + 1 : ℕ) : ℝ) ^ 2)) ≠ 0) := ne_of_gt hpos
  apply (eq_div_iff hne).2
  exact prod_weierstrass_odd_mul_half_eq_full x N

end GppOddWeierstrassProductSplit

#print axioms GppOddWeierstrassProductSplit.prod_range_even_mul_odd
#print axioms GppOddWeierstrassProductSplit.weierstrass_even_factor_rescale
#print axioms GppOddWeierstrassProductSplit.prod_weierstrass_even_rescale
#print axioms GppOddWeierstrassProductSplit.prod_weierstrass_odd_mul_even
#print axioms GppOddWeierstrassProductSplit.prod_weierstrass_odd_mul_half_eq_full
#print axioms GppOddWeierstrassProductSplit.prod_weierstrass_half_pos
#print axioms GppOddWeierstrassProductSplit.prod_weierstrass_odd_eq_full_div_half
