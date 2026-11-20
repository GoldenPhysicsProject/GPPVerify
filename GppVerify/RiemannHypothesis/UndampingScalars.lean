/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude)
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Undamping package, scalar items (c) and (d)

Scope (routed 2026-11-20, D2's undamping correction): the **scalar arithmetic** only. Nothing here is
an operator statement, a transfer identity, or a positivity claim for `Q₀`.

* (c) `epsTail_le`: for the three resolvent parameters `b ∈ {½, 3/2, 5/2}` (`Σ 2b = 9`) and
  `a = (M+1)π/L`, the signed tail constant `ε_M = Σ_b 2b/(b²+a²)` satisfies
  `0 ≤ ε_M ≤ 9 L²/((M+1)π)²`.
* (d) `undampCoeff`: the retained prime-shift coefficient `(1 − n⁻²) Λ(n) n^{−1/2}`. At `L = 18/25`
  the only `n` with `Λ(n) ≠ 0` and `log n < L` is `n = 2` (`undamp_support_eq_two`), and the
  retained scalar is `3 log 2/(4√2)` (`undampCoeff_two`, `undamp_retained_sum`).

No `sorry`, no `axiom`.
-/

namespace GppUndampingScalars

open ArithmeticFunction

/-- The signed tail constant `ε_M` for resolvent parameters `½, 3/2, 5/2` at length `L`. -/
noncomputable def epsTail (L : ℝ) (M : ℕ) : ℝ :=
  ∑ b ∈ ({1 / 2, 3 / 2, 5 / 2} : Finset ℝ), 2 * b / (b ^ 2 + ((M + 1 : ℝ) * Real.pi / L) ^ 2)

theorem sum_two_b : ∑ b ∈ ({1 / 2, 3 / 2, 5 / 2} : Finset ℝ), 2 * b = 9 := by
  rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num), Finset.sum_singleton]
  norm_num

theorem epsTail_nonneg {L : ℝ} (hL : 0 < L) (M : ℕ) : 0 ≤ epsTail L M := by
  unfold epsTail
  refine Finset.sum_nonneg fun b hb => ?_
  have : 0 < b := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl <;> norm_num
  positivity

/-- **(c), scalar part.** `ε_M ≤ 9 L² / ((M+1)π)²`. -/
theorem epsTail_le {L : ℝ} (hL : 0 < L) (M : ℕ) :
    epsTail L M ≤ 9 * L ^ 2 / (((M + 1 : ℝ)) * Real.pi) ^ 2 := by
  set a : ℝ := (M + 1 : ℝ) * Real.pi / L with ha
  have hapos : 0 < a := by positivity
  have h1 : 9 * L ^ 2 / (((M + 1 : ℝ)) * Real.pi) ^ 2 = 9 / a ^ 2 := by
    rw [ha]; field_simp
  rw [h1]
  unfold epsTail
  calc ∑ b ∈ ({1 / 2, 3 / 2, 5 / 2} : Finset ℝ), 2 * b / (b ^ 2 + a ^ 2)
      ≤ ∑ b ∈ ({1 / 2, 3 / 2, 5 / 2} : Finset ℝ), 2 * b / a ^ 2 := by
        refine Finset.sum_le_sum fun b hb => ?_
        have : 0 < b := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl <;> norm_num
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [sq_nonneg b])
    _ = 9 / a ^ 2 := by rw [← Finset.sum_div, sum_two_b]

/-- The retained prime-shift coefficient `(1 − n⁻²) Λ(n) n^{−1/2}`. -/
noncomputable def undampCoeff (n : ℕ) : ℝ :=
  (1 - ((n : ℝ) ^ 2)⁻¹) * Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ))

/-- At `L = 18/25` the only `n` with `Λ(n) ≠ 0` and `log n < L` is `n = 2`. -/
theorem undamp_support_eq_two {n : ℕ} (hΛ : Λ n ≠ 0) (hlog : Real.log n < 18 / 25) : n = 2 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hΛ
  have hn1 : n ≠ 1 := by rintro rfl; simp at hΛ
  have hn2 : 2 ≤ n := by omega
  have hn3 : n < 3 := by
    by_contra h
    push Not at h
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast h
    have hl : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) h3
    have he : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    linarith
  omega

theorem undampCoeff_two : undampCoeff 2 = 3 * Real.log 2 / (4 * Real.sqrt 2) := by
  unfold undampCoeff
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have h : ((2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt 2 := by
    rw [Nat.cast_ofNat, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, one_div]
  rw [h]
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  push_cast
  field_simp
  norm_num

/-- At `L = 18/25` the retained prime-shift scalar is exactly the `n = 2` term. -/
theorem undamp_retained_sum :
    ∑' n : ℕ, (if Real.log n < 18 / 25 then undampCoeff n else 0)
      = 3 * Real.log 2 / (4 * Real.sqrt 2) := by
  rw [tsum_eq_single 2]
  · rw [if_pos, undampCoeff_two]
    have : Real.log 2 < 18 / 25 := by
      have := Real.log_two_lt_d9
      linarith
    exact_mod_cast this
  · intro n hn
    by_cases hl : Real.log n < 18 / 25
    · rw [if_pos hl]
      unfold undampCoeff
      by_cases hΛ : Λ n = 0
      · simp [hΛ]
      · exact absurd (undamp_support_eq_two hΛ hl) hn
    · rw [if_neg hl]

end GppUndampingScalars

#print axioms GppUndampingScalars.epsTail_le
#print axioms GppUndampingScalars.undamp_support_eq_two
#print axioms GppUndampingScalars.undampCoeff_two
#print axioms GppUndampingScalars.undamp_retained_sum
