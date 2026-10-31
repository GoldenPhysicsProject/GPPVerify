import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# Elementary gamma surplus: `e^{y/2}/(2 sinh y) ≥ 1/(2y) + 1/6` on `(0, 1]`

Source: Codex/Discovery2, GPP-bridge PR #11 comment 2026-10-31 ("exact gamma surplus": for
`y ∈ (0,1]`, `e^{y/2}/(2 sinh y) ≥ 1/(2y) + 1/6`, used to improve the completed gamma jump
`J_gamma ≥ Σ (H_n + L/6)|a_n|²`). Daniel Toupin / Golden Physics Project, with AI assistance from
Codex (statement) and Claude Code (formalization).

* `sinh_le_poly`: for `0 ≤ y ≤ 1`, `sinh y ≤ y + y³/6 + y⁵/120 + y⁷/5040 + y⁸·9/322560`
  (from Mathlib's `Real.exp_bound` at `±y`, `n = 8`).
* `gamma_surplus`: for `0 < y ≤ 1`, `1/(2y) + 1/6 ≤ e^{y/2}/(2 sinh y)`.

**Scope.** The elementary real inequality only. The constant `11/50` on `(0, 7/10]` from Codex's
later comment, the completed Weil form, the triangle variance integral and the Legendre spectrum are
not formalized. No claim about RH.
-/

set_option autoImplicit false

open Finset

namespace GppGammaSurplus

/-- Upper polynomial bound for `sinh` on `[0, 1]`. -/
theorem sinh_le_poly {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    Real.sinh y ≤ y + y ^ 3 / 6 + y ^ 5 / 120 + y ^ 7 / 5040 + y ^ 8 * (9 / 322560) := by
  have ha : |y| ≤ 1 := by rwa [abs_of_nonneg h0]
  have hb : |-y| ≤ 1 := by rwa [abs_neg]
  have e1 := Real.exp_bound ha (n := 8) (by norm_num)
  have e2 := Real.exp_bound hb (n := 8) (by norm_num)
  rw [abs_neg] at e2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.succ_eq_add_one] at e1 e2
  rw [abs_of_nonneg h0] at e1 e2
  have h8 : |y| ^ 8 = y ^ 8 := by rw [abs_of_nonneg h0]
  rw [abs_le] at e1 e2
  rw [Real.sinh_eq]
  norm_num at e1 e2
  nlinarith [e1.1, e1.2, e2.1, e2.2, pow_nonneg h0 8]

/-- The gamma surplus. -/
theorem gamma_surplus {y : ℝ} (h0 : 0 < y) (h1 : y ≤ 1) :
    1 / (2 * y) + 1 / 6 ≤ Real.exp (y / 2) / (2 * Real.sinh y) := by
  have hs : 0 < Real.sinh y := Real.sinh_pos_iff.mpr h0
  have hsp := sinh_le_poly h0.le h1
  have hex : 1 + y / 2 + (y / 2) ^ 2 / 2 + (y / 2) ^ 3 / 6 ≤ Real.exp (y / 2) := by
    have := Real.sum_le_exp_of_nonneg (x := y / 2) (by positivity) 4
    simpa [Finset.sum_range_succ, Nat.factorial] using this
  rw [div_add_div _ _ (by positivity) (by norm_num), div_le_div_iff₀ (by positivity) (by positivity)]
  have hy2 : y ^ 2 ≤ y := by nlinarith
  have hy3 : y ^ 3 ≤ y ^ 2 := by nlinarith [sq_nonneg y]
  have hy4 : y ^ 4 ≤ y ^ 3 := by nlinarith [pow_nonneg h0.le 3]
  have hy5 : y ^ 5 ≤ y ^ 4 := by nlinarith [pow_nonneg h0.le 4]
  have hy6 : y ^ 6 ≤ y ^ 5 := by nlinarith [pow_nonneg h0.le 5]
  have hy7 : y ^ 7 ≤ y ^ 6 := by nlinarith [pow_nonneg h0.le 6]
  have hy8 : y ^ 8 ≤ y ^ 7 := by nlinarith [pow_nonneg h0.le 7]
  have hy9 : y ^ 9 ≤ y ^ 8 := by nlinarith [pow_nonneg h0.le 8]
  nlinarith [mul_le_mul_of_nonneg_left hsp (by positivity : (0 : ℝ) ≤ 2 * y + 2 / 3 * y ^ 2),
    mul_pos h0 hs]

end GppGammaSurplus
