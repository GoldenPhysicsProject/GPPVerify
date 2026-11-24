/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Two-sided rational enclosures of `log` and `arctan`

These are explicit finite sums with explicit remainders, stated so that `norm_num`, after
`Finset.sum_range_succ`, can certify numerical facts such as `0.6931471805 < log 2` or
`arctan (1/2) < 0.4636476091`.

## Logarithm

For `1 ≤ x`, put `u = (x - 1)/(x + 1)`, so `0 ≤ u < 1` and `x = (1 + u)/(1 - u)`. The series
`log x = 2 Σ_k u^(2k+1)/(2k+1)` has nonnegative terms, so every partial sum is a lower bound
(`Real.sum_le_log`). The tail beyond `n` terms is at most `2 u^(2n+1) / ((2n+1)(1 - u²))`,
by comparison with a geometric series (`Real.log_le_sum_add`). For `0 < x < 1`, use
`log x = -log x⁻¹`.

## Arctangent

For `0 ≤ x < 1`, the series `arctan x = Σ_n (-1)^n x^(2n+1)/(2n+1)` is alternating with
decreasing terms. Its even partial sums are lower bounds (`Real.sum_le_arctan`) and its odd
partial sums are upper bounds (`Real.arctan_le_sum`). For `x > 1`, use
`arctan x = π/2 - arctan x⁻¹` (`Real.arctan_inv_of_pos`).

## Practical size

`norm_num [Finset.sum_range_succ]` closes the examples below. They use 11 (`log 2`),
18 (`log 3`) and 17–18 (`arctan (1/2)`) terms.
-/

open Finset Filter

namespace Real

/-- The `n`-th partial sum of `2 Σ_k u^(2k+1)/(2k+1)`. -/
noncomputable def logSeriesSum (u : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, 2 * (1 / (2 * (k : ℝ) + 1)) * u ^ (2 * k + 1)

theorem hasSum_log_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    HasSum (fun k : ℕ => 2 * (1 / (2 * (k : ℝ) + 1)) * ((x - 1) / (x + 1)) ^ (2 * k + 1))
      (log x) := by
  have hx1 : 0 < x + 1 := by linarith
  have hu : |(x - 1) / (x + 1)| < 1 := by
    rw [abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - 1), abs_of_pos hx1,
      div_lt_one hx1]
    linarith
  have h := hasSum_log_sub_log_of_abs_lt_one hu
  have e : log (1 + (x - 1) / (x + 1)) - log (1 - (x - 1) / (x + 1)) = log x := by
    have h1 : 1 + (x - 1) / (x + 1) = 2 * x / (x + 1) := by field_simp; ring
    have h2 : 1 - (x - 1) / (x + 1) = 2 / (x + 1) := by field_simp; ring
    rw [h1, h2, ← log_div (by positivity) (by positivity)]
    congr 1; field_simp
  rwa [e] at h

/-- **Lower bound for `log`.** For `1 ≤ x`, every partial sum of the series is at most
`log x`. -/
theorem sum_le_log {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    logSeriesSum ((x - 1) / (x + 1)) n ≤ log x := by
  have hu : 0 ≤ (x - 1) / (x + 1) := div_nonneg (by linarith) (by linarith)
  refine sum_le_hasSum (range n) (fun k _ => ?_) (hasSum_log_of_one_le hx)
  positivity

/-- **Upper bound for `log`.** For `1 ≤ x`, with `u = (x-1)/(x+1)`,
`log x ≤ (partial sum to n) + 2 u^(2n+1) / ((2n+1)(1 - u²))`. -/
theorem log_le_sum_add {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    log x ≤ logSeriesSum ((x - 1) / (x + 1)) n +
      2 * ((x - 1) / (x + 1)) ^ (2 * n + 1) /
        ((2 * (n : ℝ) + 1) * (1 - ((x - 1) / (x + 1)) ^ 2)) := by
  set u : ℝ := (x - 1) / (x + 1) with hu_def
  have hx1 : 0 < x + 1 := by linarith
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hx1.le
  have hu1 : u < 1 := by rw [hu_def, div_lt_one hx1]; linarith
  have hu2 : u ^ 2 < 1 := by nlinarith
  have hS := hasSum_log_of_one_le hx
  rw [← hu_def] at hS
  have htail := (hasSum_nat_add_iff' n).mpr hS
  -- comparison series: (2/(2n+1)) u^(2n+1) (u²)^k
  have hgeo : HasSum (fun k : ℕ => 2 / (2 * (n : ℝ) + 1) * u ^ (2 * n + 1) * (u ^ 2) ^ k)
      (2 / (2 * (n : ℝ) + 1) * u ^ (2 * n + 1) * (1 - u ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hu2).mul_left _
  have hle := hasSum_le (fun k => ?_) htail hgeo
  · have e : 2 / (2 * (n : ℝ) + 1) * u ^ (2 * n + 1) * (1 - u ^ 2)⁻¹ =
        2 * u ^ (2 * n + 1) / ((2 * (n : ℝ) + 1) * (1 - u ^ 2)) := by
      have : (0 : ℝ) < 1 - u ^ 2 := by linarith
      field_simp
    rw [e] at hle
    unfold logSeriesSum
    linarith
  · -- termwise: 2/(2(k+n)+1) u^(2(k+n)+1) ≤ 2/(2n+1) u^(2n+1) (u²)^k
    have hpow : u ^ (2 * (k + n) + 1) = u ^ (2 * n + 1) * (u ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; ring_nf
    rw [hpow]
    have hk : (2 * (n : ℝ) + 1) ≤ 2 * ((k + n : ℕ) : ℝ) + 1 := by push_cast; linarith
    have hpos : 0 ≤ u ^ (2 * n + 1) * (u ^ 2) ^ k := by positivity
    have h1 : 1 / (2 * ((k + n : ℕ) : ℝ) + 1) ≤ 1 / (2 * (n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hk
    calc 2 * (1 / (2 * ((k + n : ℕ) : ℝ) + 1)) * (u ^ (2 * n + 1) * (u ^ 2) ^ k)
        ≤ 2 * (1 / (2 * (n : ℝ) + 1)) * (u ^ (2 * n + 1) * (u ^ 2) ^ k) := by gcongr
      _ = 2 / (2 * (n : ℝ) + 1) * u ^ (2 * n + 1) * (u ^ 2) ^ k := by ring

/-- The terms `x^(2n+1)/(2n+1)` of the arctangent series. -/
noncomputable def arctanTerm (x : ℝ) (n : ℕ) : ℝ := x ^ (2 * n + 1) / (2 * (n : ℝ) + 1)

theorem arctanTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Antitone (arctanTerm x) := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  unfold arctanTerm
  have hp : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hd : (2 * (n : ℝ) + 1) ≤ 2 * ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
  calc x ^ (2 * (n + 1) + 1) / (2 * ((n + 1 : ℕ) : ℝ) + 1)
      ≤ x ^ (2 * n + 1) / (2 * ((n + 1 : ℕ) : ℝ) + 1) := by gcongr
    _ ≤ x ^ (2 * n + 1) / (2 * (n : ℝ) + 1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hd

theorem tendsto_arctan_partial {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * arctanTerm x i) atTop (nhds (arctan x)) := by
  have h := (hasSum_arctan (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)).tendsto_sum_nat
  refine h.congr (fun n => sum_congr rfl (fun i _ => ?_))
  unfold arctanTerm; push_cast; ring

/-- **Lower bound for `arctan`.** For `0 ≤ x < 1`, the even partial sums are at most
`arctan x`. -/
theorem sum_le_arctan {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1) ^ i * arctanTerm x i ≤ arctan x :=
  Antitone.alternating_series_le_tendsto (tendsto_arctan_partial hx0 hx1)
    (arctanTerm_antitone hx0 hx1.le) k

/-- **Upper bound for `arctan`.** For `0 ≤ x < 1`, the odd partial sums are at least
`arctan x`. -/
theorem arctan_le_sum {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    arctan x ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * arctanTerm x i :=
  Antitone.tendsto_le_alternating_series (tendsto_arctan_partial hx0 hx1)
    (arctanTerm_antitone hx0 hx1.le) k

/-! ### Worked enclosures -/

example : 0.6931471805 < log 2 := by
  have h := sum_le_log (x := 2) (by norm_num) 11
  unfold logSeriesSum at h
  norm_num [Finset.sum_range_succ] at h
  linarith

example : log 2 < 0.6931471806 := by
  have h := log_le_sum_add (x := 2) (by norm_num) 11
  unfold logSeriesSum at h
  norm_num [Finset.sum_range_succ] at h
  linarith

example : 1.0986122886 < log 3 := by
  have h := sum_le_log (x := 3) (by norm_num) 18
  unfold logSeriesSum at h
  norm_num [Finset.sum_range_succ] at h
  linarith

example : log 3 < 1.0986122887 := by
  have h := log_le_sum_add (x := 3) (by norm_num) 18
  unfold logSeriesSum at h
  norm_num [Finset.sum_range_succ] at h
  linarith

example : 0.4636476090 < arctan (1 / 2) := by
  have h := sum_le_arctan (x := 1 / 2) (by norm_num) (by norm_num) 9
  norm_num [Finset.sum_range_succ, arctanTerm] at h
  linarith

example : arctan (1 / 2) < 0.4636476091 := by
  have h := arctan_le_sum (x := 1 / 2) (by norm_num) (by norm_num) 8
  norm_num [Finset.sum_range_succ, arctanTerm] at h
  linarith

end Real
