import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The Haar valuation law and the Casimir-weighted mass series

Source: Codex, GPPDiscovery2 `research/2026-09-26_profinite_internal_mass_law.md`, §§1–3 (the exact
single-prime facts and the convergence of the mean-mass series).

For `X ~ Haar(Ẑ)` the valuations `N_p = v_p(X)` are independent with the geometric law
`Pr(N_p = a) = (1 − p^{-1}) p^{-a}`. Write `q = 1/p`.

* `geometric_normalization`: `Σ_a (1 − q) q^a = 1`;
* `geometric_mean`: `E N_p = Σ_a a (1 − q) q^a = q/(1 − q) = 1/(p − 1)`;
* `geometric_laplace`: `E e^{-t μ N_p} = Σ_a (1 − q) q^a e^{-s a} = (1 − q)/(1 − q e^{-s})`, with
  `s = t μ_p`, the single-prime Laplace transform;
* `mean_mass_summable`: with the finite-place mass `μ_p = 2/√(p − 1)`, the mean total mass
  `E 𝓜 / M_* = 2 Σ_p 1/(p − 1)^{3/2}` converges (`C₁`), the series of means being summable over primes.

## Checks and scope

All claims check (the numerical value `C₁ ≈ 3.4368` is not asserted here). **Not formalized:** the
Haar measure on `Ẑ`, independence of the valuations, the Borel–Cantelli statement that a typical
profinite integer has infinitely many occupied places, the variance `p/(p − 1)²` (needs the second
moment of the geometric law), almost-sure finiteness of `𝓜`, and the product formula for the Laplace
transform. The dark-matter reading is the note's hypothesis. No RH claim.
-/

open Real

namespace GppHaarValuation

/-- **Normalization of the geometric valuation law.** -/
theorem geometric_normalization (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun a : ℕ => (1 - q) * q ^ a) 1 := by
  have := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (1 - q)
  have h : (1 - q) * (1 - q)⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  rwa [h] at this

/-- **Mean valuation.** `Σ_a a (1 − q) q^a = q/(1 − q)`. -/
theorem geometric_mean (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun a : ℕ => (a : ℝ) * ((1 - q) * q ^ a)) (q / (1 - q)) := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)).mul_left (1 - q)
  have e : (fun a : ℕ => (a : ℝ) * ((1 - q) * q ^ a)) = fun a : ℕ => (1 - q) * ((a : ℝ) * q ^ a) := by
    funext a; ring
  rw [e]
  have hne : 1 - q ≠ 0 := by linarith
  have : (1 - q) * (q / (1 - q) ^ 2) = q / (1 - q) := by field_simp
  rwa [this] at h

/-- At `q = 1/p` the mean is `1/(p − 1)`. -/
theorem mean_prime (p : ℝ) (hp : 1 < p) : 1 / p / (1 - 1 / p) = 1 / (p - 1) := by
  have : p ≠ 0 := by linarith
  have h : p - 1 ≠ 0 := by linarith
  field_simp

/-- **Single-prime Laplace transform.** -/
theorem geometric_laplace (q s : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hs : 0 ≤ s) :
    HasSum (fun a : ℕ => (1 - q) * q ^ a * Real.exp (-s * a))
      ((1 - q) / (1 - q * Real.exp (-s))) := by
  have hE : Real.exp (-s) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hE0 : 0 < Real.exp (-s) := Real.exp_pos _
  have hr0 : 0 ≤ q * Real.exp (-s) := by positivity
  have hr1 : q * Real.exp (-s) < 1 := by nlinarith
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 - q)
  have e : (fun a : ℕ => (1 - q) * q ^ a * Real.exp (-s * a)) =
      fun a => (1 - q) * (q * Real.exp (-s)) ^ a := by
    funext a
    rw [mul_pow, mul_assoc, ← Real.exp_nat_mul]
    congr 2
    ring_nf
  rw [e]
  rwa [← div_eq_mul_inv] at h

/-- **The mean-mass series converges**: `Σ_p 2/(p − 1)^{3/2} < ∞`. -/
theorem mean_mass_summable :
    Summable (fun p : Nat.Primes => 2 * ((p : ℝ) - 1) ^ (-(3 / 2 : ℝ))) := by
  have hs : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (hs.mul_left (2 * 2 ^ (3 / 2 : ℝ)))
  · have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
    have : 0 < (p : ℝ) - 1 := by linarith
    positivity
  · have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
    have hp0 : 0 < (p : ℝ) := by linarith
    have hp1 : 0 < (p : ℝ) - 1 := by linarith
    -- (p-1) ≥ p/2, so (p-1)^(-3/2) ≤ (p/2)^(-3/2) = 2^(3/2) p^(-3/2)
    have hle : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
    have h1 : ((p : ℝ) - 1) ^ (-(3 / 2 : ℝ)) ≤ ((p : ℝ) / 2) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)
    have h2 : ((p : ℝ) / 2) ^ (-(3 / 2 : ℝ)) = 2 ^ (3 / 2 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.div_rpow hp0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg hp0.le]
      field_simp
    calc 2 * ((p : ℝ) - 1) ^ (-(3 / 2 : ℝ))
        ≤ 2 * (2 ^ (3 / 2 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 2 * 2 ^ (3 / 2 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by ring

end GppHaarValuation
