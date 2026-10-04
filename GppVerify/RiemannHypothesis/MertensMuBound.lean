import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The elementary Möbius bound `|Σ_{d ≤ x} μ(d)/d| ≤ 2`

Source: Codex, `research/codex/2026-10-03_totient_energy_and_golden_dilation.md`, §7.

* `mu_floor_sum`: `Σ_{d ≤ N} μ(d) ⌊N/d⌋ = 1` for `N ≥ 1`;
* `mu_inv_sum_bound`: for real `x ≥ 1`, `|Σ_{d ≤ ⌊x⌋} μ(d)/d| ≤ 2` (via `x m(x) = 1 + Σ μ(d){x/d}`).

## Checks and scope

Both claims check; this is the classical elementary argument, with no prime number theorem and no
RH. **Not formalized:** the rest of the note's §7 (the Bessel-series bound `|B(y)| ≤ C y^{-1/2}` and
the resulting `|K(x)| = O(1)`), and §§2–3 (the inner-function / Hardy-space energy identities).
No RH claim.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace GppMertensMu

/-- `Σ_{d ≤ N} μ(d) ⌊N/d⌋ = 1`. -/
theorem mu_floor_sum (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Ioc 0 N, (μ d : ℤ) * ((N / d : ℕ) : ℤ) = 1 := by
  have h1 : ∀ d ∈ Ioc 0 N, (μ d : ℤ) * ((N / d : ℕ) : ℤ) =
      ∑ x ∈ (Ioc 0 N).filter (d ∣ ·), (μ d : ℤ) := by
    intro d _
    rw [Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl h1]
  have h2 : ∑ d ∈ Ioc 0 N, ∑ x ∈ (Ioc 0 N).filter (d ∣ ·), (μ d : ℤ) =
      ∑ x ∈ Ioc 0 N, ∑ d ∈ x.divisors, (μ d : ℤ) := by
    refine Finset.sum_comm' ?_
    intro d x
    simp only [Finset.mem_Ioc, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
      exact ⟨⟨h5, by omega⟩, h3, h4⟩
    · rintro ⟨⟨h5, h6⟩, h3, h4⟩
      have := Nat.le_of_dvd (by omega) h5
      exact ⟨⟨Nat.pos_of_dvd_of_pos h5 (by omega), by omega⟩, ⟨h3, h4⟩, h5⟩
  rw [h2]
  have h3 : ∀ x ∈ Ioc 0 N, ∑ d ∈ x.divisors, (μ d : ℤ) = if x = 1 then 1 else 0 := by
    intro x _
    have := DFunLike.congr_fun (moebius_mul_coe_zeta : (μ * ζ : ArithmeticFunction ℤ) = 1) x
    rw [coe_mul_zeta_apply] at this
    rw [this]
    simp [ArithmeticFunction.one_apply]
  rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq']
  simp [hN]

/-- **`|Σ_{d ≤ x} μ(d)/d| ≤ 2` for `x ≥ 1`.** -/
theorem mu_inv_sum_bound (x : ℝ) (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊x⌋₊, (μ d : ℝ) / d| ≤ 2 := by
  set N := ⌊x⌋₊ with hN
  have hx0 : 0 < x := by linarith
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  -- x * m(x) = Σ μ(d) x/d = Σ μ(d) (⌊x/d⌋ + frac(x/d)) = 1 + Σ μ(d) frac(x/d)
  have hdec : ∀ d ∈ Ioc 0 N, (μ d : ℝ) * (x / d) =
      (μ d : ℝ) * ((N / d : ℕ) : ℝ) + (μ d : ℝ) * Int.fract (x / d) := by
    intro d hd
    have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
    have hfl : ⌊x / d⌋₊ = N / d := Nat.floor_div_natCast x d
    have hfl' : ((⌊x / d⌋₊ : ℕ) : ℝ) = ⌊x / d⌋ := by
      rw [← Int.natCast_floor_eq_floor (div_nonneg hx0.le (Nat.cast_nonneg d))]; push_cast; rfl
    have : ((N / d : ℕ) : ℝ) + Int.fract (x / d) = x / d := by
      rw [← hfl, hfl', Int.fract]; ring
    rw [← mul_add, this]
  have hsum : x * ∑ d ∈ Ioc 0 N, (μ d : ℝ) / d =
      1 + ∑ d ∈ Ioc 0 N, (μ d : ℝ) * Int.fract (x / d) := by
    have h1 : x * ∑ d ∈ Ioc 0 N, (μ d : ℝ) / d = ∑ d ∈ Ioc 0 N, (μ d : ℝ) * (x / d) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => by ring
    rw [h1, Finset.sum_congr rfl hdec, Finset.sum_add_distrib]
    congr 1
    have h := congrArg (Int.cast : ℤ → ℝ) (mu_floor_sum N hN1)
    push_cast at h
    exact h
  have hbound : |∑ d ∈ Ioc 0 N, (μ d : ℝ) * Int.fract (x / d)| ≤ N := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ d ∈ Ioc 0 N, |(μ d : ℝ) * Int.fract (x / d)| ≤ 1 := by
      intro d _
      rw [abs_mul]
      have hmu : |(μ d : ℝ)| ≤ 1 := by
        have := abs_moebius_le_one (n := d)
        exact_mod_cast this
      have hf : |Int.fract (x / d)| ≤ 1 := by
        rw [abs_of_nonneg (Int.fract_nonneg _)]; exact (Int.fract_lt_one _).le
      calc |(μ d : ℝ)| * |Int.fract (x / d)| ≤ 1 * 1 :=
            mul_le_mul hmu hf (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    calc ∑ d ∈ Ioc 0 N, |(μ d : ℝ) * Int.fract (x / d)| ≤ ∑ d ∈ Ioc 0 N, (1 : ℝ) :=
          Finset.sum_le_sum this
      _ = N := by simp
  have habs : |x * ∑ d ∈ Ioc 0 N, (μ d : ℝ) / d| ≤ 1 + x := by
    rw [hsum]
    calc |1 + ∑ d ∈ Ioc 0 N, (μ d : ℝ) * Int.fract (x / d)|
        ≤ |(1 : ℝ)| + |∑ d ∈ Ioc 0 N, (μ d : ℝ) * Int.fract (x / d)| := abs_add_le _ _
      _ ≤ 1 + x := by rw [abs_one]; linarith
  rw [abs_mul, abs_of_pos hx0] at habs
  rw [← mul_le_mul_iff_of_pos_left hx0]
  nlinarith [abs_nonneg (∑ d ∈ Ioc 0 N, (μ d : ℝ) / d)]

end GppMertensMu
