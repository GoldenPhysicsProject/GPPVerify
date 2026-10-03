import GppVerify.RiemannHypothesis.SU11PrimeBlaschke
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Prime TFD phase geometry: Carathéodory function, local variance, Fisher distance

Source: Codex, GPPDiscovery2 `research/2026-09-27_prime_tfd_phase_fisher_mass_geometry.md`,
§§3, 4 (local second moment), 6 (radial Fisher distance and negativity).

* `caratheodory_re`: for `z = r e^{iθ}`, `|r| < 1`, `Re ((1 + z)/(1 − z)) = P_r(θ) > 0` (`H` is a
  Carathéodory function, and its real part is the phase intensity of the prime TFD state);
* `euler_log_deriv`: `L z/(1 − z) = (L/2) H(z) − L/2`: the local Euler logarithmic derivative is a
  positive-real function minus its vacuum baseline;
* `local_variance`: each prime contributes the second moment `Σ_m ½ (L r^m)² = L²/(2(p − 1))` to the
  variance of the centered current (`r² = 1/p`);
* `fisher_radial_distance`: `∫₀^r √2/(1 − u²) du = √2 · artanh r`: the radial Fisher distance from the
  uniform state is `√2 κ`;
* `negativity_eq`: the pure two-mode logarithmic negativity `E_N = 2κ` satisfies `E_N = √2 · D_F`.

## Checks and scope

All claims checked. **Not formalized:** the Fisher information integrals `I_rr = 2/(1−r²)²`, `I_φφ`
(and hence the curvature `K_F = −2`), the phase POVM resolution, the equidistribution of the finite-prime
flow on the torus (the long-time mean `0` and autocorrelation), and the entanglement interpretation.
Only the *local* second moment is formalized, not the ergodic average. No RH claim.
-/

open GppSU11Prime

namespace GppPrimeTfdPhase

/-- **`H(z) = (1+z)/(1−z)` has real part the Poisson kernel.** -/
theorem caratheodory_re (r θ : ℝ) (hr : |r| < 1) :
    ((1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) /
        (1 - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re = poisson r θ := by
  have hd := den_pos r θ hr
  set z : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hz
  have hre : z.re = r * Real.cos θ := by
    simp [hz, Complex.exp_ofReal_mul_I_re]
  have him : z.im = r * Real.sin θ := by
    simp [hz, Complex.exp_ofReal_mul_I_im]
  have hnsq : Complex.normSq (1 - z) = 1 - 2 * r * Real.cos θ + r ^ 2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hre, him, Complex.one_re,
      Complex.one_im]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hnum : (1 + z).re * (1 - z).re + (1 + z).im * (1 - z).im = 1 - r ^ 2 := by
    simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
      Complex.sub_im, hre, him]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [Complex.div_re, ← add_div, hnum, hnsq, poisson]

theorem caratheodory_pos (r θ : ℝ) (hr : |r| < 1) :
    0 < ((1 + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) /
        (1 - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re := by
  rw [caratheodory_re r θ hr, poisson]
  have hd := den_pos r θ hr
  have : 0 < 1 - r ^ 2 := by nlinarith [abs_lt.mp hr, sq_abs r]
  positivity

/-- **The local Euler logarithmic derivative is positive-real minus its vacuum baseline.** -/
theorem euler_log_deriv (L : ℝ) (z : ℂ) (hz : 1 - z ≠ 0) :
    (L : ℂ) * (z / (1 - z)) = (L : ℂ) / 2 * ((1 + z) / (1 - z)) - (L : ℂ) / 2 := by
  field_simp
  ring

/-- **Local second moment.** With `r² = 1/p`: `Σ_{m ≥ 1} ½ (L r^m)² = L² / (2 (p − 1))`. -/
theorem local_variance (p L : ℝ) (hp : 1 < p) :
    HasSum (fun m : ℕ => (1 / 2 : ℝ) * (L * (p ^ (-(1 / 2 : ℝ))) ^ (m + 1)) ^ 2)
      (L ^ 2 / (2 * (p - 1))) := by
  have hp0 : 0 < p := by linarith
  have hr2 : (p ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
    rw [Real.rpow_neg_one]
  set q : ℝ := 1 / p with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one hp0]; exact hp
  have hg := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left (L ^ 2 / 2 * q)
  have e : (fun m : ℕ => (1 / 2 : ℝ) * (L * (p ^ (-(1 / 2 : ℝ))) ^ (m + 1)) ^ 2) =
      fun m => L ^ 2 / 2 * q * q ^ m := by
    funext m
    rw [mul_pow, ← pow_mul, show (m + 1) * 2 = 2 * (m + 1) by ring, pow_mul, hr2, pow_succ]
    ring
  rw [e]
  have hval : L ^ 2 / 2 * q * (1 - q)⁻¹ = L ^ 2 / (2 * (p - 1)) := by
    rw [hq]
    have : p - 1 ≠ 0 := by linarith
    have h2 : 1 - 1 / p = (p - 1) / p := by field_simp
    rw [h2]
    field_simp
  rwa [hval] at hg

/-- **Radial Fisher distance.** `∫₀^r √2/(1 − u²) du = √2 · artanh r`. -/
theorem fisher_radial_distance (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ u in (0 : ℝ)..r, Real.sqrt 2 / (1 - u ^ 2) = Real.sqrt 2 * Real.artanh r := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) r,
      HasDerivAt (fun u : ℝ => Real.sqrt 2 * ((Real.log (1 + u) - Real.log (1 - u)) / 2))
        (Real.sqrt 2 / (1 - u ^ 2)) u := by
    intro u hu
    rw [Set.uIcc_of_le hr0] at hu
    have h1 : 0 < 1 + u := by linarith [hu.1]
    have h2 : 0 < 1 - u := by linarith [hu.2]
    have d1 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + u)) u := by
      have := ((hasDerivAt_id u).const_add 1).log h1.ne'
      simpa using this
    have d2 : HasDerivAt (fun u : ℝ => Real.log (1 - u)) (-1 / (1 - u)) u := by
      have := ((hasDerivAt_id u).const_sub 1).log h2.ne'
      simpa using this
    have d3 := ((d1.sub d2).div_const 2).const_mul (Real.sqrt 2)
    refine d3.congr_deriv ?_
    have h3 : 1 - u ^ 2 = (1 - u) * (1 + u) := by ring
    rw [h3]
    field_simp
    ring
  have hcont : IntervalIntegrable (fun u : ℝ => Real.sqrt 2 / (1 - u ^ 2)) MeasureTheory.volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro u hu
    rw [Set.uIcc_of_le hr0] at hu
    have : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
    exact this.ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
  have hm : r ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, hr1.le⟩
  rw [Real.artanh_eq_half_log hm]
  have h1 : 0 < 1 + r := by linarith
  have h2 : 0 < 1 - r := by linarith
  simp only [add_zero, sub_zero, Real.log_one, sub_self, zero_div, mul_zero]
  rw [Real.log_div h1.ne' h2.ne']
  ring

/-- **Negativity is `√2` times the Fisher distance.** With `D_F = √2 κ`: `2κ = √2 · D_F`. -/
theorem negativity_eq (κ : ℝ) : 2 * κ = Real.sqrt 2 * (Real.sqrt 2 * κ) := by
  rw [← mul_assoc, Real.mul_self_sqrt (by norm_num)]

end GppPrimeTfdPhase
