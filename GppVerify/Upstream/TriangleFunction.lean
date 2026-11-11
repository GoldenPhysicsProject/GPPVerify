/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Golden Eye)
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The triangle (Fejér) function `max (a - |x|) 0`

Mathlib-style lemmas staged for upstreaming (see `README.md`). For `a > 0`, the triangle
`x ↦ max (a - |x|) 0` is the self-convolution `1_{[-a/2, a/2]} ∗ 1_{[-a/2, a/2]}`. It is the
Fejér kernel in x-space and the standard Lipschitz test function in explicit-formula arguments.

* `Real.continuous_max_sub_abs`: it is continuous.
* `Real.max_sub_abs_eq_zero_of_le`: it vanishes for `a ≤ |x|`.
* `Real.integral_max_sub_abs`: `∫ x, max (a - |x|) 0 = a ^ 2` for `0 ≤ a`.
-/

open Set MeasureTheory

namespace Real

theorem continuous_max_sub_abs (a : ℝ) : Continuous fun x : ℝ => max (a - |x|) 0 := by
  fun_prop

theorem max_sub_abs_eq_zero_of_le {a x : ℝ} (h : a ≤ |x|) : max (a - |x|) 0 = 0 :=
  max_eq_right (sub_nonpos.2 h)

theorem integral_max_sub_abs {a : ℝ} (ha : 0 ≤ a) : ∫ x, max (a - |x|) 0 = a ^ 2 := by
  have hout : ∀ x, x ∉ Ioc (-a) a → max (a - |x|) 0 = 0 := fun x hx => by
    apply max_sub_abs_eq_zero_of_le
    rcases not_and_or.1 hx with h | h
    · rw [abs_of_nonpos (by linarith [not_lt.1 h])]; linarith [not_lt.1 h]
    · rw [abs_of_pos (by linarith [not_le.1 h])]; linarith [not_le.1 h]
  have hc := continuous_max_sub_abs a
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout,
    ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hl : EqOn (fun x : ℝ => max (a - |x|) 0) (fun x => a + x) (uIcc (-a) 0) := fun x hx => by
    rw [uIcc_of_le (by linarith)] at hx
    simp only
    rw [abs_of_nonpos hx.2, max_eq_left (by linarith [hx.1])]; ring
  have hr : EqOn (fun x : ℝ => max (a - |x|) 0) (fun x => a - x) (uIcc 0 a) := fun x hx => by
    rw [uIcc_of_le ha] at hx
    simp only
    rw [abs_of_nonneg hx.1, max_eq_left (by linarith [hx.2])]
  rw [intervalIntegral.integral_congr hl, intervalIntegral.integral_congr hr,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => a * x + x ^ 2 / 2)
      (fun x _ => by
        convert ((hasDerivAt_id' x).const_mul a).add ((hasDerivAt_pow 2 x).div_const 2) using 1
        · rfl
        · norm_num)
      ((by fun_prop : Continuous fun x : ℝ => a + x).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => a * x - x ^ 2 / 2)
      (fun x _ => by
        convert ((hasDerivAt_id' x).const_mul a).sub ((hasDerivAt_pow 2 x).div_const 2) using 1
        · rfl
        · norm_num)
      ((by fun_prop : Continuous fun x : ℝ => a - x).intervalIntegrable _ _)]
  ring

end Real
