import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The prime thermofield-double dictionary

Source: Codex / Discovery2, `research/2026-09-26_prime_tfd_modular_horizon_dictionary.md` §§1, 2, 5
(`GPPDiscovery2`, `codex/discovery-workbench`). Daniel Toupin / Golden Physics Project, with AI
assistance from Codex (statements) and Claude Code (formalization).

For a real `p > 1` (a prime in the application) let `x = 1/p` and `κ_p = arsinh (1/√(p − 1))`.

* `geometric_trace`: the Haar valuation law `(1 − 1/p) p^{−a}` is a probability distribution:
  `Σ_{a ≥ 0} (1 − 1/p) p^{−a} = 1`.
* `tanh_kappa`: `tanh κ_p = p^{−1/2}`.
* `tfd_norm`: `(1/cosh² κ_p) Σ_a tanh(κ_p)^{2a} = 1` (normalisation of the purification).
* `mean_occupation`: `Σ_a a (1 − 1/p) p^{−a} = 1/(p − 1) = sinh² κ_p`.
* `mass_sq`: with `μ_p = 2 sinh κ_p`, `μ_p² = 4/(p − 1) = 4/(e^{log p} − 1)`, and
  `log p = log(1 + 4/μ_p²)`.
* `mu_eq_one_iff`: `μ_p = 1 ↔ p = 5`; and `sinh κ_5 = 1/2`, `κ_5 = log φ` with `φ = (1+√5)/2`.

**Scope.** The one-oscillator algebra only. The identification of the arithmetic and geometric
modular generators (§§3–4), the global TFD and Hagedorn boundary (§6) and every physical
interpretation in the note are not formalized. No claim about RH.
-/

set_option autoImplicit false

open Real

namespace GppPrimeTfd

/-- Squeezing parameter `κ_p = arsinh(1/√(p−1))`. -/
noncomputable def kappa (p : ℝ) : ℝ := Real.arsinh (1 / Real.sqrt (p - 1))

lemma sinh_kappa (p : ℝ) (_hp : 1 < p) : Real.sinh (kappa p) = 1 / Real.sqrt (p - 1) := by
  unfold kappa; exact Real.sinh_arsinh _

lemma sinh_kappa_sq (p : ℝ) (hp : 1 < p) : Real.sinh (kappa p) ^ 2 = 1 / (p - 1) := by
  rw [sinh_kappa p hp, div_pow, Real.sq_sqrt (by linarith)]; simp

lemma cosh_kappa_sq (p : ℝ) (hp : 1 < p) : Real.cosh (kappa p) ^ 2 = p / (p - 1) := by
  have h := Real.cosh_sq (kappa p)
  rw [h, sinh_kappa_sq p hp]
  have h1 : p - 1 ≠ 0 := by linarith
  field_simp; ring

/-- The Haar valuation law is a probability distribution. -/
theorem geometric_trace (p : ℝ) (hp : 1 < p) :
    ∑' a : ℕ, (1 - 1 / p) * (1 / p) ^ a = 1 := by
  have hx0 : 0 ≤ 1 / p := by positivity
  have hx1 : 1 / p < 1 := by rw [div_lt_one (by linarith)]; exact hp
  rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 hx1]
  have : 1 - 1 / p ≠ 0 := by linarith
  exact mul_inv_cancel₀ this

/-- `tanh κ_p = p^{−1/2}`. -/
theorem tanh_kappa (p : ℝ) (hp : 1 < p) : Real.tanh (kappa p) = 1 / Real.sqrt p := by
  have hc : 0 < Real.cosh (kappa p) := Real.cosh_pos _
  have hs : 0 < Real.sqrt (p - 1) := Real.sqrt_pos.mpr (by linarith)
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  rw [Real.tanh_eq_sinh_div_cosh, sinh_kappa p hp]
  have hcosh : Real.cosh (kappa p) = Real.sqrt p / Real.sqrt (p - 1) := by
    rw [← Real.sqrt_div (by linarith : (0:ℝ) ≤ p), eq_comm]
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) hc.le]
    nlinarith [cosh_kappa_sq p hp]
  rw [hcosh]
  field_simp

/-- The TFD purification is normalised: `(1/cosh² κ) Σ_a (tanh κ)^{2a} = 1`. -/
theorem tfd_norm (p : ℝ) (hp : 1 < p) :
    (1 / Real.cosh (kappa p) ^ 2) * ∑' a : ℕ, (Real.tanh (kappa p) ^ 2) ^ a = 1 := by
  have h1 : Real.tanh (kappa p) ^ 2 = 1 / p := by
    rw [tanh_kappa p hp, div_pow, Real.sq_sqrt (by linarith)]; simp
  have hx0 : 0 ≤ 1 / p := by positivity
  have hx1 : 1 / p < 1 := by rw [div_lt_one (by linarith)]; exact hp
  rw [h1, tsum_geometric_of_lt_one hx0 hx1, cosh_kappa_sq p hp]
  have : p - 1 ≠ 0 := by linarith
  have : 1 - 1 / p ≠ 0 := by
    have : 1 / p < 1 := hx1
    linarith
  field_simp

/-- Mean occupation: `Σ_a a (1 − 1/p) p^{−a} = 1/(p − 1) = sinh² κ_p`. -/
theorem mean_occupation (p : ℝ) (hp : 1 < p) :
    ∑' a : ℕ, (a : ℝ) * ((1 - 1 / p) * (1 / p) ^ a) = Real.sinh (kappa p) ^ 2 := by
  have hx1 : ‖(1 / p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_lt_one (by linarith)]; exact hp
  have h := tsum_coe_mul_geometric_of_norm_lt_one hx1
  have e : ∀ a : ℕ, (a : ℝ) * ((1 - 1 / p) * (1 / p) ^ a) =
      (1 - 1 / p) * ((a : ℝ) * (1 / p) ^ a) := fun a => by ring
  simp_rw [e]
  rw [tsum_mul_left, h, sinh_kappa_sq p hp]
  have h1 : p - 1 ≠ 0 := by linarith
  have h2 : 1 - 1 / p ≠ 0 := by
    have : 1 / p < 1 := by rw [div_lt_one (by linarith)]; exact hp
    linarith
  field_simp

/-- Casimir mass `μ_p = 2 sinh κ_p`: `μ_p² = 4/(p − 1)`. -/
noncomputable def mu (p : ℝ) : ℝ := 2 * Real.sinh (kappa p)

theorem mass_sq (p : ℝ) (hp : 1 < p) : mu p ^ 2 = 4 / (p - 1) := by
  unfold mu
  rw [mul_pow, sinh_kappa_sq p hp]
  ring

/-- Modular energy `E = log p` satisfies `μ² = 4/(e^E − 1)` and `E = log(1 + 4/μ²)`. -/
theorem energy_of_mass (p : ℝ) (hp : 1 < p) :
    mu p ^ 2 = 4 / (Real.exp (Real.log p) - 1) ∧ Real.log p = Real.log (1 + 4 / mu p ^ 2) := by
  have hp0 : 0 < p := by linarith
  have hm : mu p ^ 2 = 4 / (p - 1) := mass_sq p hp
  refine ⟨by rw [Real.exp_log hp0]; exact hm, ?_⟩
  rw [hm]
  have : p - 1 ≠ 0 := by linarith
  congr 1
  field_simp
  ring

/-- `μ_p = 1 ↔ p = 5` for `p > 1`. -/
theorem mu_eq_one_iff (p : ℝ) (hp : 1 < p) : mu p = 1 ↔ p = 5 := by
  have hsq := mass_sq p hp
  have hmu : 0 ≤ mu p := by
    unfold mu; have := Real.sinh_nonneg_iff.mpr (Real.arsinh_nonneg_iff.mpr
      (by positivity : (0:ℝ) ≤ 1 / Real.sqrt (p - 1))); positivity
  constructor
  · intro h
    rw [h] at hsq
    have h1 : p - 1 ≠ 0 := by linarith
    field_simp at hsq
    linarith
  · intro h
    subst h
    have : mu 5 ^ 2 = 1 := by rw [hsq]; norm_num
    nlinarith [hmu]

/-- `sinh κ_5 = 1/2`. -/
theorem sinh_kappa_five : Real.sinh (kappa 5) = 1 / 2 := by
  rw [sinh_kappa 5 (by norm_num)]
  have : Real.sqrt (5 - 1) = 2 := by
    rw [show (5 : ℝ) - 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [this]

/-- `κ_5 = log φ`, `φ = (1 + √5)/2`. -/
theorem kappa_five : kappa 5 = Real.log ((1 + Real.sqrt 5) / 2) := by
  unfold kappa
  have h4 : Real.sqrt (5 - 1) = 2 := by
    rw [show (5 : ℝ) - 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4, Real.arsinh]
  congr 1
  have h5 : Real.sqrt (1 + (1 / 2) ^ 2) = Real.sqrt 5 / 2 := by
    rw [show (1 : ℝ) + (1 / 2) ^ 2 = 5 / 4 by norm_num, Real.sqrt_div (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [show (1 / 2 : ℝ) = 1 / 2 from rfl]
  simp only [one_div]
  rw [show (1 + (2⁻¹ : ℝ) ^ 2) = 1 + (1 / 2) ^ 2 by simp, h5]
  ring

end GppPrimeTfd
