import GppVerify.QuantumGravity.SinhWeierstrassNormalized
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import GppVerify.QuantumGravity.OddWeierstrassProductSplit
import Mathlib.Tactic

/-!
# Odd Weierstrass quotient limit

This module combines the exact finite odd/even quotient with the normalized
`sinh` Weierstrass limit.  The removable point `x = 0` is deliberately left
out of the quotient theorem; it will be restored when the limiting ratio is
identified with `cosh (π x / 2)`.
-/

namespace GppOddWeierstrassQuotientLimit

open Filter Topology
open scoped BigOperators

/-- The doubling map on natural numbers is cofinal at `atTop`. -/
theorem tendsto_two_mul_atTop :
    Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  exact Filter.eventually_atTop.2 ⟨b, by
    intro a ha
    omega⟩

/-- Away from the removable point `x = 0`, the odd positive-denominator
    Weierstrass product converges to the quotient of the two normalized sinh
    products. -/
theorem tendsto_odd_weierstrass_to_sinh_quotient (x : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∏ k ∈ Finset.range n,
          ((1 : ℝ) + x ^ 2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)))
      Filter.atTop
      (𝓝
        ((Real.sinh (Real.pi * x) / (Real.pi * x)) /
          (Real.sinh (Real.pi * (x / 2)) / (Real.pi * (x / 2))))) := by
  have hnum0 :=
    GppSinhWeierstrassNormalized.tendsto_prod_one_add_sq_div_normalized x hx
  have hnum := hnum0.comp tendsto_two_mul_atTop
  have hxhalf : x / 2 ≠ 0 := div_ne_zero hx (by norm_num)
  have hden :=
    GppSinhWeierstrassNormalized.tendsto_prod_one_add_sq_div_normalized (x / 2) hxhalf
  have harg : Real.pi * (x / 2) ≠ 0 := mul_ne_zero Real.pi_ne_zero hxhalf
  have hsinh : Real.sinh (Real.pi * (x / 2)) ≠ 0 := by
    rcases lt_or_gt_of_ne hxhalf with hneg | hpos
    · exact
        (Real.sinh_neg_iff.mpr
          (mul_neg_of_pos_of_neg Real.pi_pos hneg)).ne
    · exact
        (Real.sinh_pos_iff.mpr
          (mul_pos Real.pi_pos hpos)).ne'
  have hdenlim :
      Real.sinh (Real.pi * (x / 2)) / (Real.pi * (x / 2)) ≠ 0 :=
    div_ne_zero hsinh harg
  have hdiv := hnum.div hden hdenlim
  have hfun :
      (fun n : ℕ =>
        ∏ k ∈ Finset.range n,
          ((1 : ℝ) + x ^ 2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2))) =
      (fun n : ℕ =>
        ((∏ j ∈ Finset.range (2 * n),
            ((1 : ℝ) + x ^ 2 / (((j + 1 : ℕ) : ℝ) ^ 2))) /
          ∏ k ∈ Finset.range n,
            ((1 : ℝ) + (x / 2) ^ 2 / (((k + 1 : ℕ) : ℝ) ^ 2)))) := by
    funext n
    exact
      GppOddWeierstrassProductSplit.prod_weierstrass_odd_eq_full_div_half x n
  rw [hfun]
  exact hdiv.congr fun n => by simp [Function.comp_apply]

end GppOddWeierstrassQuotientLimit

#print axioms GppOddWeierstrassQuotientLimit.tendsto_two_mul_atTop
#print axioms GppOddWeierstrassQuotientLimit.tendsto_odd_weierstrass_to_sinh_quotient
