import GppVerify.QuantumGravity.OddWeierstrassQuotientLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# Odd Weierstrass product and the cosh limit

This module removes the normalized-sinh quotient from the odd-product limit and
restores the removable point `x = 0`.  The result is the exact global finite-product
limit needed for the chamber logarithm and odd-lattice tanh closure.
-/

namespace GppOddWeierstrassCoshLimit

open Filter Topology
open scoped BigOperators

/-- Away from `x = 0`, the normalized sinh quotient is exactly the hyperbolic cosine. -/
theorem sinh_normalized_quotient_eq_cosh (x : ℝ) (hx : x ≠ 0) :
    ((Real.sinh (Real.pi * x) / (Real.pi * x)) /
      (Real.sinh (Real.pi * (x / 2)) / (Real.pi * (x / 2)))) =
      Real.cosh (Real.pi * x / 2) := by
  have hxhalf : x / 2 ≠ 0 := div_ne_zero hx (by norm_num)
  have hy : Real.pi * (x / 2) ≠ 0 := mul_ne_zero Real.pi_ne_zero hxhalf
  have hsinh : Real.sinh (Real.pi * (x / 2)) ≠ 0 := by
    rcases lt_or_gt_of_ne hxhalf with hneg | hpos
    · exact
        (Real.sinh_neg_iff.mpr
          (mul_neg_of_pos_of_neg Real.pi_pos hneg)).ne
    · exact
        (Real.sinh_pos_iff.mpr
          (mul_pos Real.pi_pos hpos)).ne'
  have hdouble : Real.pi * x = 2 * (Real.pi * (x / 2)) := by ring
  rw [hdouble, Real.sinh_two_mul]
  field_simp [hy, hsinh]
  <;> ring

/-- The finite odd positive-denominator Weierstrass product converges globally to
    `cosh (π x / 2)`. -/
theorem tendsto_odd_weierstrass_to_cosh (x : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∏ k ∈ Finset.range n,
          ((1 : ℝ) + x ^ 2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)))
      Filter.atTop
      (𝓝 (Real.cosh (Real.pi * x / 2))) := by
  by_cases hx : x = 0
  · subst x
    simpa using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 (1 : ℝ)))
  · have h :=
      GppOddWeierstrassQuotientLimit.tendsto_odd_weierstrass_to_sinh_quotient x hx
    rw [sinh_normalized_quotient_eq_cosh x hx] at h
    simpa only [div_eq_mul_inv, mul_assoc] using h

end GppOddWeierstrassCoshLimit

#print axioms GppOddWeierstrassCoshLimit.sinh_normalized_quotient_eq_cosh
#print axioms GppOddWeierstrassCoshLimit.tendsto_odd_weierstrass_to_cosh
