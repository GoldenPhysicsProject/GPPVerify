/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A sharp lower bound for a difference of logarithms

For `0 < y < x`,

  `2 (x - y) / (x + y) ≤ log x - log y`.

This is the first term of the series `log (1 + 1/a) = 2 Σ_k 1/((2k+1)(2a+1)^(2k+1))`
(`Real.hasSum_log_one_add_inv`), at `a = y / (x - y)`. It is sharper than the bound
`(x - y) / x ≤ log x - log y` coming from `Real.log_le_sub_one_of_pos`: the two agree to first
order in `x - y`, but this one is also exact to second order. That is what a sum-versus-integral
comparison with a telescoping error needs.
-/

namespace Real

/-- **The sharp logarithm bound.** For `0 < y < x`, `2 (x - y) / (x + y) ≤ log x - log y`. -/
theorem two_mul_sub_div_add_le_log_sub_log {x y : ℝ} (hy : 0 < y) (hxy : y < x) :
    2 * (x - y) / (x + y) ≤ log x - log y := by
  set c : ℝ := y / (x - y) with hc
  have hxy' : 0 < x - y := sub_pos.mpr hxy
  have hc0 : 0 < c := div_pos hy hxy'
  have hterm0 : 2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * (1 / (2 * c + 1)) ^ (2 * 0 + 1)
      ≤ log (1 + c⁻¹) := by
    refine le_hasSum (hasSum_log_one_add_inv hc0) 0 (fun k _ => ?_)
    have : 0 < 2 * c + 1 := by linarith
    positivity
  have h1 : 1 + c⁻¹ = x / y := by
    rw [hc, inv_div]; field_simp; ring
  rw [h1, log_div (by linarith) hy.ne'] at hterm0
  have h2 : 2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * (1 / (2 * c + 1)) ^ (2 * 0 + 1)
      = 2 * (x - y) / (x + y) := by
    rw [hc]; field_simp; ring
  linarith [h2 ▸ hterm0]

end Real
