/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Golden Eye)
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Bounds on `log π`

Mathlib-style lemmas staged for upstreaming (see `README.md`). These are companions to
`Real.log_two_gt_d9` and `Real.log_three_gt_d9`. They follow from `Real.pi_gt_d6` /
`Real.pi_lt_d6`, the bounds on `exp 1`, and the Taylor bound `Real.exp_bound'`.

* `Real.log_pi_gt_d2 : 1.14 < log π`
* `Real.log_pi_lt_d2 : log π < 1.15`
-/

namespace Real

theorem log_pi_gt_d2 : 1.14 < log π := by
  rw [lt_log_iff_exp_lt pi_pos]
  have hb := exp_bound' (x := 0.14) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  have hsplit : exp 1.14 = exp 1 * exp 0.14 := by rw [← exp_add]; norm_num
  rw [hsplit]
  have hE := exp_one_lt_d9
  have := pi_gt_d6
  nlinarith [mul_le_mul hE.le hb (exp_pos _).le (by norm_num), exp_pos 0.14]

theorem log_pi_lt_d2 : log π < 1.15 := by
  rw [log_lt_iff_lt_exp pi_pos]
  have hs := sum_le_exp_of_nonneg (x := 0.15) (by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  have hsplit : exp 1.15 = exp 1 * exp 0.15 := by rw [← exp_add]; norm_num
  rw [hsplit]
  have hE := exp_one_gt_d9
  have := pi_lt_d6
  nlinarith [mul_le_mul hE.le hs (by norm_num) (exp_pos _).le]

end Real
