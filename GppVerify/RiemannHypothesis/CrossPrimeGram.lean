import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.GCD.Basic

/-!
# Two Gram kernels on the integers: real dilation versus independent primes

Source: Codex, `research/codex/2026-10-03_totient_energy_and_golden_dilation.md`, §§5–6.

For positive integers `m, n`:
* the real-dilation orbit has Gram kernel `C_real(m,n) = √(min(m,n)/max(m,n))`;
* the independent-prime kernel is `C_prime(m,n) = gcd(m,n)/√(mn)`.

Results:
* `creal_eq_cprime_mul`: `C_real = C_prime · (min/gcd)`, so the ratio is `min(m,n)/gcd(m,n)`;
* `creal_eq_cprime_iff`: `C_real(m,n) = C_prime(m,n)` iff `m ∣ n` or `n ∣ m` (they agree exactly on
  divisibility chains, in particular on every single prime-power ladder);
* `example_two_three`: `C_real(2,3) = √(2/3)` while `C_prime(2,3) = 1/√6`, a factor `2`;
* `blaschke_mul_neg`, `blaschke_zero`: the real-symmetric Blaschke pair
  `B_a(s) = (s−a)(s−ā)/((s+ā)(s+a))` satisfies `B_a(s) B_a(−s) = 1` and `B_a(0) = 1`.

## Checks and scope

All claims check. The note defines `C_prime` as the product of local prime covariances
`∏_p p^{-|v_p(m)-v_p(n)|/2}`; here `C_prime` is taken in its stated closed form `gcd/√(mn)`, and the
product formula is **not formalized**. **Not formalized:** the Hardy-space proof that the totient
response `K` is an `L²` dilation orbit with correlations `1/(2r)` (§§2–3), the global golden-channel
realization (§4, whose reflection identities are in `PrimeHouseholder`), and the claim that the Blaschke
factor is inner and breaks the tail criterion (§6, analytic). Nothing here asserts or refutes RH.
-/

open Real

namespace GppCrossPrimeGram

/-- Real-dilation Gram kernel. -/
noncomputable def creal (m n : ℕ) : ℝ := Real.sqrt ((min m n : ℕ) / (max m n : ℕ))

/-- Independent-prime Gram kernel (closed form). -/
noncomputable def cprime (m n : ℕ) : ℝ := (Nat.gcd m n : ℝ) / Real.sqrt ((m : ℝ) * n)

theorem creal_eq_cprime_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    creal m n = cprime m n * ((min m n : ℕ) / (Nat.gcd m n : ℝ)) := by
  unfold creal cprime
  have hmn : ((m : ℝ) * n) = ((min m n : ℕ) : ℝ) * ((max m n : ℕ) : ℝ) := by
    rcases le_total m n with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]; ring
  have hmin : (0 : ℝ) < (min m n : ℕ) := by exact_mod_cast lt_min hm hn
  have hmax : (0 : ℝ) < (max m n : ℕ) := by exact_mod_cast lt_max_of_lt_left hm
  have hg : (0 : ℝ) < (Nat.gcd m n : ℕ) := by exact_mod_cast Nat.gcd_pos_of_pos_left n hm
  rw [hmn, Real.sqrt_mul hmin.le, Real.sqrt_div hmin.le]
  have h1 : 0 < Real.sqrt ((min m n : ℕ) : ℝ) := Real.sqrt_pos.mpr hmin
  have h2 : 0 < Real.sqrt ((max m n : ℕ) : ℝ) := Real.sqrt_pos.mpr hmax
  have h3 : Real.sqrt ((min m n : ℕ) : ℝ) * Real.sqrt ((min m n : ℕ) : ℝ) = ((min m n : ℕ) : ℝ) :=
    Real.mul_self_sqrt hmin.le
  field_simp
  rw [sq]; exact h3

theorem creal_eq_cprime_iff (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    creal m n = cprime m n ↔ (m ∣ n ∨ n ∣ m) := by
  have hg : (0 : ℝ) < (Nat.gcd m n : ℕ) := by exact_mod_cast Nat.gcd_pos_of_pos_left n hm
  have hcp : 0 < cprime m n := by
    unfold cprime
    have : (0 : ℝ) < (m : ℝ) * n := by positivity
    exact div_pos hg (Real.sqrt_pos.mpr this)
  rw [creal_eq_cprime_mul m n hm hn]
  constructor
  · intro h
    have h1 : ((min m n : ℕ) : ℝ) / (Nat.gcd m n : ℝ) = 1 := by
      have := mul_left_cancel₀ hcp.ne' (by linarith [h] : cprime m n * (((min m n : ℕ) : ℝ) / (Nat.gcd m n : ℝ)) = cprime m n * 1)
      exact this
    have h2 : ((min m n : ℕ) : ℝ) = (Nat.gcd m n : ℝ) := by
      field_simp at h1; exact h1
    have h3 : min m n = Nat.gcd m n := by exact_mod_cast h2
    rcases le_total m n with hle | hle
    · rw [min_eq_left hle] at h3
      left; rw [h3]; exact Nat.gcd_dvd_right m n
    · rw [min_eq_right hle] at h3
      right; rw [h3]; exact Nat.gcd_dvd_left m n
  · intro h
    have hmg : min m n = Nat.gcd m n := by
      rcases h with h | h
      · rw [Nat.gcd_eq_left h]; exact min_eq_left (Nat.le_of_dvd hn h)
      · rw [Nat.gcd_eq_right h]; exact min_eq_right (Nat.le_of_dvd hm h)
    rw [hmg, div_self hg.ne', mul_one]

/-- `C_real(2,3) = √(2/3)` while `C_prime(2,3) = 1/√6`. -/
theorem example_two_three :
    creal 2 3 = Real.sqrt (2 / 3) ∧ cprime 2 3 = 1 / Real.sqrt 6 ∧ creal 2 3 = 2 * cprime 2 3 := by
  have h1 : creal 2 3 = Real.sqrt (2 / 3) := by
    unfold creal; norm_num
  have h2 : cprime 2 3 = 1 / Real.sqrt 6 := by
    unfold cprime
    have : Nat.gcd 2 3 = 1 := by decide
    rw [this]; norm_num
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  have h6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have h6' : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  have e : Real.sqrt (2 / 3) = 2 / Real.sqrt 6 := by
    rw [Real.sqrt_div (by norm_num), eq_div_iff h6.ne']
    have h3 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    have h3' : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    rw [← h3]
    field_simp
    nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 3 by norm_num),
      Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  rw [e]; ring

/-- The real-symmetric Blaschke factor. -/
noncomputable def blaschke (a s : ℂ) : ℂ :=
  (s - a) * (s - (starRingEnd ℂ) a) / (((s + (starRingEnd ℂ) a)) * (s + a))

theorem blaschke_mul_neg (a s : ℂ) (h1 : s + a ≠ 0) (h2 : s - a ≠ 0)
    (h3 : s + (starRingEnd ℂ) a ≠ 0) (h4 : s - (starRingEnd ℂ) a ≠ 0) :
    blaschke a s * blaschke a (-s) = 1 := by
  unfold blaschke
  have h1' : -s + a ≠ 0 := by intro h; apply h2; linear_combination -h
  have h2' : -s - a ≠ 0 := by intro h; apply h1; linear_combination -h
  have h3' : -s + (starRingEnd ℂ) a ≠ 0 := by intro h; apply h4; linear_combination -h
  have h4' : -s - (starRingEnd ℂ) a ≠ 0 := by intro h; apply h3; linear_combination -h
  field_simp
  ring

theorem blaschke_zero (a : ℂ) (ha : a ≠ 0) : blaschke a 0 = 1 := by
  unfold blaschke
  have : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
  simp
  field_simp

end GppCrossPrimeGram
