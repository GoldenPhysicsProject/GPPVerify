import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-!
# E₈ theta-series coefficients and the perfect number 496

Source: decoding_reality_v43221.tex, "E₈, Perfect Numbers, and Moonshine".
The E₈ theta series has Fourier coefficients `240·σ₃(n)` (the weight-4
Eisenstein series `E₄`), and `496 = dim(E₈)` is the third perfect number.
Both are genuinely finite divisor-sum facts, decidable via `Nat.sigma`,
verified independently in Python before being written as Lean proofs.
-/

namespace GppPerfectE8

/-- The E₈ theta-series coefficients `240·σ₃(n)` for `n = 1,...,5`
    (`σ₃(n) = Nat.sigma 3 n`, the sum of cubes of divisors). -/
theorem e8_theta_coeff_one : 240 * Nat.sigma 3 1 = 240 := by native_decide
theorem e8_theta_coeff_two : 240 * Nat.sigma 3 2 = 2160 := by native_decide
theorem e8_theta_coeff_three : 240 * Nat.sigma 3 3 = 6720 := by native_decide
theorem e8_theta_coeff_four : 240 * Nat.sigma 3 4 = 17520 := by native_decide
theorem e8_theta_coeff_five : 240 * Nat.sigma 3 5 = 30240 := by native_decide

/-- **496 is a perfect number**: `σ₁(496) = 2·496`
    (`σ₁ = Nat.sigma 1`, the sum of divisors). -/
theorem perfect_496 : Nat.sigma 1 496 = 2 * 496 := by native_decide

/-- `496 = 2⁴·31`, with `31 = 2⁵ - 1` a Mersenne prime -- the Euclid-Euler
    form `2^(p-1)(2^p - 1)` of an even perfect number, at `p = 5`. -/
theorem factorization_496 : (496 : ℕ) = 2 ^ 4 * 31 := by norm_num

theorem mersenne_31 : (31 : ℕ) = 2 ^ 5 - 1 := by norm_num

theorem mersenne_31_prime : Nat.Prime 31 := by norm_num

/-- The Euclid-Euler form: `496 = 2^(5-1) * (2^5 - 1)`. -/
theorem euclid_euler_form_496 : (496 : ℕ) = 2 ^ (5 - 1) * (2 ^ 5 - 1) := by norm_num

end GppPerfectE8
