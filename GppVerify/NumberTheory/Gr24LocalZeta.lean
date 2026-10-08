import GppVerify.NumberTheory.WeylCasimir
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Local zeta factor of `Gr(2,4)` from its point-count polynomial

`GppWeylCasimir.gr24_point_count q = 1 + q + 2q² + q³ + q⁴` is the point count of `Gr(2,4)` over
`𝔽_q` (Schubert cells: one each of dimension 0,1,3,4 and two of dimension 2).

This file proves the **local Euler factor algebra** behind the stub `open_hasse_weil_gr24_factorization`
(`ζ_Gr(s) = ζ(s)ζ(s−1)ζ(s−2)²ζ(s−3)ζ(s−4)`): for `T = p^{-s}`,

`exp(∑_{n≥1} N(pⁿ) Tⁿ / n) = 1 / ((1−T)(1−pT)(1−p²T)²(1−p³T)(1−p⁴T))`

whenever `‖p⁴T‖ < 1` (i.e. `Re s > 4`).

## Scope

Proved: the identity above, from the polynomial `N`. **Not proved here:** that
`N(q)` really is `#Gr(2,4)(𝔽_q)` (Schubert-cell counting over finite fields; Mathlib has no Grassmannian
point counts), and the passage from local factors to the global Euler product over all primes. So the
stub's *geometric* input remains a library gap; its *analytic* shape is now a theorem.
-/

open Complex

namespace GppGr24LocalZeta

/-- `∑_{n} xⁿ/n = −log(1−x)` rewritten for the exponential: `exp(∑ xⁿ/n) = (1−x)⁻¹`, `‖x‖ < 1`. -/
theorem exp_tsum_pow_div {x : ℂ} (hx : ‖x‖ < 1) :
    Complex.exp (∑' n : ℕ, x ^ n / n) = (1 - x)⁻¹ := by
  rw [(Complex.hasSum_taylorSeries_neg_log hx).tsum_eq, Complex.exp_neg,
    Complex.exp_log (by
      intro h
      have : x = 1 := by linear_combination -h
      rw [this] at hx; simp at hx)]

/-- `exp(-log(1-x)) = (1-x)⁻¹` for `‖x‖ < 1`, with the series as a `HasSum`. -/
theorem hasSum_log_aux {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => x ^ n / n) (-Complex.log (1 - x)) :=
  Complex.hasSum_taylorSeries_neg_log hx

theorem exp_neg_log_aux {x : ℂ} (hx : ‖x‖ < 1) : Complex.exp (-Complex.log (1 - x)) = (1 - x)⁻¹ := by
  rw [Complex.exp_neg, Complex.exp_log (by
      intro h
      have : x = 1 := by linear_combination -h
      rw [this] at hx; simp at hx)]

/-- **Local zeta factor of `Gr(2,4)`.** -/
theorem gr24_local_zeta (p : ℕ) (T : ℂ) (hT : ‖(p : ℂ) ^ 4 * T‖ < 1) (hp : 1 ≤ p) :
    Complex.exp (∑' n : ℕ, ((GppWeylCasimir.gr24_point_count ((p : ℤ) ^ n) : ℤ) : ℂ) * T ^ n / n)
      = ((1 - T) * (1 - p * T) * (1 - p ^ 2 * T) ^ 2 * (1 - p ^ 3 * T) * (1 - p ^ 4 * T))⁻¹ := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hle : ∀ i : ℕ, i ≤ 4 → ‖(p : ℂ) ^ i * T‖ < 1 := by
    intro i hi
    refine lt_of_le_of_lt ?_ hT
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hp1 hi) (norm_nonneg _)
  have h0 := hle 0 (by norm_num)
  have h1 := hle 1 (by norm_num)
  have h2 := hle 2 (by norm_num)
  have h3 := hle 3 (by norm_num)
  have h4 := hle 4 (by norm_num)
  simp only [pow_zero, one_mul, pow_one] at h0 h1
  have hs0 := hasSum_log_aux h0
  have hs1 := hasSum_log_aux h1
  have hs2 := hasSum_log_aux h2
  have hs3 := hasSum_log_aux h3
  have hs4 := hasSum_log_aux h4
  have hsum := (((hs0.add hs1).add (hs2.mul_left 2)).add hs3).add hs4
  have hterm : ∀ n : ℕ,
      ((GppWeylCasimir.gr24_point_count ((p : ℤ) ^ n) : ℤ) : ℂ) * T ^ n / n
        = (T ^ n / n + (↑p * T) ^ n / n) + 2 * (((p : ℂ) ^ 2 * T) ^ n / n) + ((p : ℂ) ^ 3 * T) ^ n / n
          + ((p : ℂ) ^ 4 * T) ^ n / n := by
    intro n
    simp only [GppWeylCasimir.gr24_point_count]
    push_cast
    simp only [mul_pow, ← pow_mul]
    rw [mul_comm n 2, mul_comm n 3, mul_comm n 4]
    ring
  rw [tsum_congr hterm, hsum.tsum_eq]
  simp only [Complex.exp_add]
  have e2 : Complex.exp (2 * -Complex.log (1 - (p : ℂ) ^ 2 * T))
      = ((1 - (p : ℂ) ^ 2 * T)⁻¹) ^ 2 := by
    rw [two_mul, Complex.exp_add, exp_neg_log_aux h2]; ring
  rw [e2, exp_neg_log_aux h0, exp_neg_log_aux h1, exp_neg_log_aux h3, exp_neg_log_aux h4]
  rw [mul_inv, mul_inv, mul_inv, mul_inv, inv_pow]

end GppGr24LocalZeta
