import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Cramér lower bound on the intensity of an independent prime-power channel

Source: Codex/GPP, `work/codex/2026-10-16_independent_prime_Poisson_KL_intensity_budget_no_go.md`
(PR11 comment 6216029557), in the setting of Astra's gamma-free Poisson transport
(`work/2026-10-16_astra_gamma_free_poisson_transport.md`).

For a channel with reference Poisson intensity `α > 0`, tilted mean `w > 0`, and logarithm `u`, the
Cramér rate is `I_α(w) = 2w·arsinh(w/α) − 2(√(α²+w²) − α)`. Proved here, with no probability:
* `rate_lower`: `I_α(w) ≥ 2w (log(2w/α) − 1)`;
* `alpha_lower`: if `I_α(w) ≤ w u` then `α ≥ (2/e)·w·e^{−u/2}`;
* `alpha_lower_prime_power`: with `w = Λ/√n`, `u = log n` this reads `α ≥ (2/e)·Λ/n`;
* `sinh_log_half`, `alpha_astra_mean`: Astra's choice `α = 2Λ/(n−1)` satisfies `α · sinh(log n / 2) = Λ/√n`,
  its tilted mean.

**Scope, stated plainly.** The hypothesis `I_α(w) ≤ w u` is the Gibbs/Cramér consequence of the entropy
budget `KL ≤ w u`; that `KL ≥ I_α(w)` for every law with mean `w` is a probability fact that is
**not** formalized here, and neither is the divergence of `Σ Λ(n)/n` (Mertens), which is what turns this
local bound into the "intensity budget `4` is exceeded" no-go. Nothing here concerns correlated
channels, the KMS/CFS constructions the note leaves open, or RH. No RH claim.
-/

namespace GppCramerIntensityBound

open Real

/-- The Cramér rate of the centred Poisson pair `(N₊ − N₋)/2` with intensity `α`, at mean `w`. -/
noncomputable def rate (α w : ℝ) : ℝ := 2 * w * arsinh (w / α) - 2 * (√(α ^ 2 + w ^ 2) - α)

/-- `arsinh x ≥ log (2x)` for `x > 0`. -/
theorem log_two_mul_le_arsinh {x : ℝ} (hx : 0 < x) : Real.log (2 * x) ≤ arsinh x := by
  rw [arsinh]
  apply Real.log_le_log (by positivity)
  have : x ≤ √(1 + x ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  linarith

/-- `√(α² + w²) − α ≤ w` for `α, w ≥ 0`. -/
theorem sqrt_sub_le {α w : ℝ} (hα : 0 ≤ α) (hw : 0 ≤ w) : √(α ^ 2 + w ^ 2) - α ≤ w := by
  have : √(α ^ 2 + w ^ 2) ≤ α + w := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  linarith

/-- `I_α(w) ≥ 2w (log (2w/α) − 1)`. -/
theorem rate_lower {α w : ℝ} (hα : 0 < α) (hw : 0 < w) :
    2 * w * (Real.log (2 * w / α) - 1) ≤ rate α w := by
  have h1 : Real.log (2 * (w / α)) ≤ arsinh (w / α) := log_two_mul_le_arsinh (by positivity)
  have h2 := sqrt_sub_le hα.le hw.le
  have h3 : 2 * (w / α) = 2 * w / α := by ring
  rw [h3] at h1
  unfold rate
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * w)]

/-- If the rate is within the budget `w u`, the intensity is at least `(2/e) w e^{−u/2}`. -/
theorem alpha_lower {α w u : ℝ} (hα : 0 < α) (hw : 0 < w) (h : rate α w ≤ w * u) :
    2 / Real.exp 1 * w * Real.exp (-u / 2) ≤ α := by
  have h1 := rate_lower hα hw
  have h2 : Real.log (2 * w / α) ≤ 1 + u / 2 := by
    by_contra hc
    have hc' := not_le.mp hc
    nlinarith [mul_pos hw (sub_pos.mpr hc')]
  have h3 : 2 * w / α ≤ Real.exp (1 + u / 2) := by
    calc 2 * w / α = Real.exp (Real.log (2 * w / α)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (1 + u / 2) := Real.exp_le_exp.mpr h2
  rw [div_le_iff₀ hα] at h3
  have h4 : Real.exp (1 + u / 2) = Real.exp 1 * Real.exp (u / 2) := Real.exp_add _ _
  have h5 : Real.exp (-u / 2) * Real.exp (u / 2) = 1 := by
    rw [← Real.exp_add, show -u / 2 + u / 2 = 0 by ring, Real.exp_zero]
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  rw [h4] at h3
  calc 2 / Real.exp 1 * w * Real.exp (-u / 2)
      = 2 * w * Real.exp (-u / 2) / Real.exp 1 := by ring
    _ ≤ α := by
        rw [div_le_iff₀ hpos]
        nlinarith [Real.exp_pos (-u / 2), Real.exp_pos (u / 2), h5, h3]

/-- `exp (log n / 2) = √n` for `n > 0`. -/
theorem exp_log_half {n : ℝ} (hn : 0 < n) : Real.exp (Real.log n / 2) = √n := by
  have hsq : Real.exp (Real.log n / 2) * Real.exp (Real.log n / 2) = n := by
    rw [← Real.exp_add, show Real.log n / 2 + Real.log n / 2 = Real.log n by ring,
      Real.exp_log hn]
  conv_rhs => rw [← hsq]
  rw [Real.sqrt_mul_self (Real.exp_pos _).le]

/-- Prime-power form: `w = Λ/√n`, `u = log n`, so `α ≥ (2/e) Λ / n`. -/
theorem alpha_lower_prime_power {α n Λ : ℝ} (hα : 0 < α) (hn : 1 < n) (hΛ : 0 < Λ)
    (h : rate α (Λ / √n) ≤ Λ / √n * Real.log n) : 2 / Real.exp 1 * (Λ / n) ≤ α := by
  have hn0 : 0 < n := by linarith
  have hs : 0 < √n := Real.sqrt_pos.mpr hn0
  have key := alpha_lower hα (div_pos hΛ hs) h
  have e : Real.exp (-Real.log n / 2) = 1 / √n := by
    rw [show -Real.log n / 2 = -(Real.log n / 2) by ring, Real.exp_neg, exp_log_half hn0, one_div]
  rw [e] at key
  have hnn : √n * √n = n := Real.mul_self_sqrt hn0.le
  calc 2 / Real.exp 1 * (Λ / n) = 2 / Real.exp 1 * (Λ / √n) * (1 / √n) := by
        rw [mul_assoc]; congr 1
        rw [div_mul_div_comm, mul_one, hnn]
    _ ≤ α := key

/-- `sinh (log n / 2) = (n − 1) / (2√n)` for `n > 0`. -/
theorem sinh_log_half {n : ℝ} (hn : 0 < n) : sinh (Real.log n / 2) = (n - 1) / (2 * √n) := by
  have hs : 0 < √n := Real.sqrt_pos.mpr hn
  have e1 : Real.exp (Real.log n / 2) = √n := exp_log_half hn
  have e2 : Real.exp (-(Real.log n / 2)) = 1 / √n := by
    rw [Real.exp_neg, e1, one_div]
  rw [Real.sinh_eq, e1, e2]
  field_simp
  rw [Real.sq_sqrt hn.le]

/-- Astra's choice `α = 2Λ/(n−1)` has tilted mean `α sinh(log n/2) = Λ/√n`. -/
theorem alpha_astra_mean {n Λ : ℝ} (hn : 1 < n) :
    2 * Λ / (n - 1) * sinh (Real.log n / 2) = Λ / √n := by
  have hn0 : 0 < n := by linarith
  have hs : 0 < √n := Real.sqrt_pos.mpr hn0
  rw [sinh_log_half hn0]
  have : n - 1 ≠ 0 := by linarith
  field_simp

end GppCramerIntensityBound
