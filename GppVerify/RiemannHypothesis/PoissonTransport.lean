import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Gamma-free Poisson transport: exact channel identities and the intensity budget

Source: Astra, `work/2026-10-16_astra_gamma_free_poisson_transport.md` (GPP-bridge; context
Codex PR #11 comment 6215141315). Daniel Toupin / Golden Physics Project, with AI assistance from
Astra (statement) and Claude Code (formalization).

Write `p_λ(k) = e^{−λ} λ^k / k!` for the Poisson weights.

* `poisson_total`, `poisson_mean`, `poisson_mgf`: `Σ p_λ = 1`, `Σ k p_λ(k) = λ`, and
  `Σ e^{ck} p_λ(k) = exp(λ(e^c − 1))`.
* `poisson_kl`: for `μ, λ > 0`, `Σ p_μ(k) log(p_μ(k)/p_λ(k)) = μ log(μ/λ) − μ + λ`.
* `pair_logMgf`: `λ(e^{t/2} − 1) + λ(e^{−t/2} − 1) = 2λ(cosh(t/2) − 1)`. This is the log-mgf of
  `(N₊ − N₋)/2` for independent `N± ~ Poisson(λ)` (the product of the two `poisson_mgf`s at
  `c = ±t/2`). At `λ = 4` it is Astra's `V(t) = 8(cosh(t/2) − 1)` (`V_eq`).
* `tilt_mean`, `tilt_kl`, `tilt_kl_le`: tilting a pair to rates `α e^{±u/2}` gives mean
  `(α e^{u/2} − α e^{−u/2})/2 = α sinh(u/2)` and relative entropy
  `u α sinh(u/2) − 2α(cosh(u/2) − 1) ≤ u α sinh(u/2)` for `u ≥ 0`, `α ≥ 0`.
* `alpha_eq`: for a prime-power channel `u = log n`, `w = Λ(n)/√n`, the intensity
  `α = w / sinh(u/2)` equals `2Λ(n)/(n − 1)`, for `n ≥ 2`.
* `budget_lt_four`, `budget_gt_four`: the intensities `Σ 2Λ(n)/(n−1)` over `n = 2, …, 5` sum to
  less than `4`, and adding `n = 7` exceeds `4`. So the independent-channel construction exhausts
  the fixed intensity budget `4` at the prime `7`, as the note says (floats `3.7517…`, `4.4003…`).

**Scope.** The probability layer is not built: independence, the reference law of
`Y = (N₊ − N₋)/2`, and the Gibbs variational inequality `D(Q‖P) ≥ tB − V`. The statements here
are the exact series and closed-form identities behind it. The Legendre transform
`V*(B) = 2B asinh(B/4) − 2√(B² + 16) + 8` is not formalized. No all-prime entropy bound and no
claim about RH.
-/

set_option autoImplicit false

open Real

namespace GppPoissonTransport

/-- Poisson weight `p_λ(k) = e^{−λ} λ^k / k!`. -/
noncomputable def p (lam : ℝ) (k : ℕ) : ℝ := exp (-lam) * (lam ^ k / k.factorial)

lemma hasSum_exp (x : ℝ) : HasSum (fun n : ℕ => x ^ n / n.factorial) (exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

theorem poisson_total (lam : ℝ) : HasSum (p lam) 1 := by
  have h := (hasSum_exp lam).mul_left (exp (-lam))
  rwa [← exp_add, neg_add_cancel, exp_zero] at h

theorem poisson_mgf (lam c : ℝ) :
    HasSum (fun k : ℕ => exp (c * k) * p lam k) (exp (lam * (exp c - 1))) := by
  have h := (hasSum_exp (lam * exp c)).mul_left (exp (-lam))
  rw [← exp_add, show -lam + lam * exp c = lam * (exp c - 1) by ring] at h
  refine h.congr_fun fun k => ?_
  simp only [p, mul_pow, ← exp_nat_mul]
  rw [show (k : ℝ) * c = c * k by ring]; ring

theorem poisson_mean (lam : ℝ) : HasSum (fun k : ℕ => (k : ℝ) * p lam k) lam := by
  have h := (poisson_total lam).mul_left lam
  rw [mul_one] at h
  refine (hasSum_nat_add_iff' 1).mp ?_
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
  refine h.congr_fun fun k => ?_
  simp only [p, Nat.factorial_succ, Nat.cast_mul, pow_succ]
  push_cast
  field_simp

theorem poisson_kl {mu lam : ℝ} (hmu : 0 < mu) (hlam : 0 < lam) :
    HasSum (fun k : ℕ => p mu k * Real.log (p mu k / p lam k))
      (mu * Real.log (mu / lam) - mu + lam) := by
  have hratio : ∀ k : ℕ, Real.log (p mu k / p lam k) = (lam - mu) + k * Real.log (mu / lam) := by
    intro k
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    have : p mu k / p lam k = exp (lam - mu) * (mu / lam) ^ k := by
      simp only [p]
      rw [div_pow, show lam - mu = -mu - -lam by ring, exp_sub]
      field_simp
    rw [this, Real.log_mul (exp_pos _).ne' (pow_pos (div_pos hmu hlam) _).ne', Real.log_exp,
      Real.log_pow]
  have h1 := (poisson_total mu).mul_left (lam - mu)
  have h2 := (poisson_mean mu).mul_left (Real.log (mu / lam))
  have := h1.add h2
  rw [show (lam - mu) * 1 + Real.log (mu / lam) * mu = mu * Real.log (mu / lam) - mu + lam by
    ring] at this
  refine this.congr_fun fun k => ?_
  rw [hratio]; ring

theorem pair_logMgf (lam t : ℝ) :
    lam * (exp (t / 2) - 1) + lam * (exp (-(t / 2)) - 1) = 2 * lam * (cosh (t / 2) - 1) := by
  rw [cosh_eq]; ring

/-- Astra's reference `V(t) = 4(e^{t/2} + e^{−t/2} − 2) = 8(cosh(t/2) − 1)`. -/
theorem V_eq (t : ℝ) :
    4 * (exp (t / 2) - 1) + 4 * (exp (-(t / 2)) - 1) = 8 * (cosh (t / 2) - 1) := by
  rw [pair_logMgf]; ring

theorem tilt_mean (α u : ℝ) : (α * exp (u / 2) - α * exp (-(u / 2))) / 2 = α * sinh (u / 2) := by
  rw [sinh_eq]; ring

/-- Relative entropy of the tilted pair (sum of the two Poisson `poisson_kl` values). -/
theorem tilt_kl {α : ℝ} (hα : 0 < α) (u : ℝ) :
    (α * exp (u / 2) * Real.log (α * exp (u / 2) / α) - α * exp (u / 2) + α) +
      (α * exp (-(u / 2)) * Real.log (α * exp (-(u / 2)) / α) - α * exp (-(u / 2)) + α) =
      u * (α * sinh (u / 2)) - 2 * α * (cosh (u / 2) - 1) := by
  rw [mul_div_cancel_left₀ _ hα.ne', mul_div_cancel_left₀ _ hα.ne', Real.log_exp, Real.log_exp,
    sinh_eq, cosh_eq]
  ring

theorem tilt_kl_le {α u : ℝ} (hα : 0 ≤ α) :
    u * (α * sinh (u / 2)) - 2 * α * (cosh (u / 2) - 1) ≤ u * (α * sinh (u / 2)) := by
  have := one_le_cosh (u / 2)
  nlinarith

/-- The channel intensity: `(Λ(n)/√n) / sinh(log n / 2) = 2Λ(n)/(n − 1)` for `n ≥ 2`. -/
theorem alpha_eq {n : ℕ} (hn : 2 ≤ n) (L : ℝ) :
    (L / Real.sqrt n) / sinh (Real.log n / 2) = 2 * L / ((n : ℝ) - 1) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hr : exp (Real.log n / 2) = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]; ring_nf
  have hs : sinh (Real.log n / 2) = ((n : ℝ) - 1) / (2 * Real.sqrt n) := by
    have hsq := Real.sq_sqrt hpos.le
    have hsp : 0 < Real.sqrt n := Real.sqrt_pos.mpr hpos
    rw [sinh_eq, exp_neg, hr]
    field_simp
    linear_combination hsq
  have hsp : 0 < Real.sqrt n := Real.sqrt_pos.mpr hpos
  rw [hs]
  field_simp

lemma log_three_bounds : 1 / 3 + Real.log 2 ≤ Real.log 3 ∧ Real.log 3 ≤ 1 / 2 + Real.log 2 := by
  have h : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hu := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
  have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
  constructor <;> [skip; skip] <;> rw [h] <;> norm_num at hu hl ⊢ <;> linarith

lemma log_five_bounds : 1 / 5 + 2 * Real.log 2 ≤ Real.log 5 ∧
    Real.log 5 ≤ 1 / 4 + 2 * Real.log 2 := by
  have h : Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4) := by
    rw [show (5 : ℝ) = 2 ^ 2 * (5 / 4) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; norm_num
  have hu := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
  have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
  constructor <;> rw [h] <;> norm_num at hu hl ⊢ <;> linarith

lemma log_seven_ge : 3 * Real.log 2 - 1 / 7 ≤ Real.log 7 := by
  have h : Real.log 7 = 3 * Real.log 2 - Real.log (8 / 7) := by
    rw [show (7 : ℝ) = 2 ^ 3 / (8 / 7) by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; norm_num
  have hu := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 / 7 by norm_num)
  rw [h]; norm_num at hu ⊢; linarith

open scoped ArithmeticFunction.vonMangoldt in
/-- The intensities `α_n = 2Λ(n)/(n − 1)` for `n = 2, 3, 4, 5` (`Λ(4) = log 2`). -/
lemma budget_terms :
    2 * Λ 2 / (2 - 1) + 2 * Λ 3 / (3 - 1) + 2 * Λ 4 / (4 - 1) + 2 * Λ 5 / (5 - 1) =
      2 * Real.log 2 + Real.log 3 + 2 * Real.log 2 / 3 + Real.log 5 / 2 := by
  have h4 : Λ 4 = Real.log 2 := by
    have : Λ (2 ^ 2) = Real.log 2 := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      push_cast; rfl
    simpa using this
  rw [h4, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 5)]
  push_cast; ring

open scoped ArithmeticFunction.vonMangoldt in
/-- **Budget not yet exhausted through `n = 5`:** `Σ_{n=2}^{5} 2Λ(n)/(n−1) < 4`. -/
theorem budget_lt_four :
    2 * Λ 2 / (2 - 1) + 2 * Λ 3 / (3 - 1) + 2 * Λ 4 / (4 - 1) + 2 * Λ 5 / (5 - 1) < (4 : ℝ) := by
  rw [budget_terms]
  have := log_three_bounds.2; have := log_five_bounds.2; have := Real.log_two_lt_d9
  linarith

open scoped ArithmeticFunction.vonMangoldt in
/-- **Budget exceeded once `7` is added:** `Σ_{n=2}^{5} 2Λ(n)/(n−1) + 2Λ(7)/6 > 4`. -/
theorem budget_gt_four :
    (4 : ℝ) < 2 * Λ 2 / (2 - 1) + 2 * Λ 3 / (3 - 1) + 2 * Λ 4 / (4 - 1) + 2 * Λ 5 / (5 - 1) +
      2 * Λ 7 / (7 - 1) := by
  rw [budget_terms, ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 7)]
  have := log_three_bounds.1; have := log_five_bounds.1; have := log_seven_ge
  have := Real.log_two_gt_d9
  simp only [Nat.cast_ofNat]
  linarith

end GppPoissonTransport
