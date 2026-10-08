import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The pole-neutral dyadic filter: exact algebra

Source: Astra, `work/2026-10-08_astra_pole_neutral_collision_closure.md` §§1–3 (GPPDiscovery3
`experiments/pole_neutral_window`). With `a = log 2`, `c = cosh(a/2) = 3/(2√2)` and the unit box `b`, the
even step function `φ = T_a b + T_{−a} b − 2c b` has bilateral transform `Φ(z) = 2(cosh(az) − c) B(z)`.
This file proves the exact scalar facts:

* `cosh_half_log_two`: `cosh(log 2/2) = 3/(2√2)`;
* `filter_vanishes_half`: the factor `2(cosh(az) − c)` vanishes at `z = ±1/2` (the two pole labels);
* `filter_zero_iff`: it vanishes only when `|Re z| = 1/2`, so it removes **no** centred zero with
  `0 < |Re z| < 1/2` (`filter_ne_zero_of_off_axis`);
* `filter_square_expansion`: `4(cosh(az) − c)² = 13/2 − 3√2 (e^{az} + e^{−az}) + (e^{2az} + e^{−2az})`, the
  five-scale coefficients `(13/2, −3√2, 1)` of `h_φ`;
* `norm_sq_filter`: `‖φ‖² = 2 + (3/√2)² = 13/2`;
* `pole_cancellation`: `13/2 − 3√2(√2 + 1/√2) + (2 + 1/2) = 0`, the cancellation of the `A√x` pole term in
  `T(x)`.

## Scope

Exact elementary algebra. The Weil explicit formula, the identity `C_φ(log x) = −T(x) − D_φ(log x)`, and the
lower bound `T(x) ≥ −K` (which the note proves is *equivalent* to RH) are not formalized; that lower bound is
open. No RH claim.
-/

open Complex

namespace GppPoleNeutral

/-- `a = log 2`. -/
noncomputable def a : ℝ := Real.log 2

/-- `c = cosh(a/2)`. -/
noncomputable def c : ℝ := Real.cosh (a / 2)

theorem a_pos : 0 < a := Real.log_pos (by norm_num)

theorem exp_half_a : Real.exp (a / 2) = Real.sqrt 2 := by
  rw [a, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  congr 1; ring

theorem cosh_half_log_two : c = 3 / (2 * Real.sqrt 2) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  unfold c
  rw [Real.cosh_eq, Real.exp_neg, exp_half_a]
  field_simp
  nlinarith [h2]

/-- The filter factor `2(cosh(az) − c)`. -/
noncomputable def factor (z : ℂ) : ℂ := 2 * (Complex.cosh (a * z) - c)

theorem filter_vanishes_half : factor (1 / 2) = 0 ∧ factor (-1 / 2) = 0 := by
  constructor
  · unfold factor c
    have : (a : ℂ) * (1 / 2) = ((a / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_cosh]; simp
  · unfold factor c
    have : (a : ℂ) * (-1 / 2) = -((a / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.cosh_neg, ← Complex.ofReal_cosh]; simp

/-- **The filter vanishes only on `|Re z| = 1/2`.** -/
theorem filter_zero_iff {z : ℂ} (h : factor z = 0) : z.re = 1 / 2 ∨ z.re = -1 / 2 := by
  have hc : Complex.cosh (a * z) = c := by
    unfold factor at h
    have := mul_eq_zero.mp h
    rcases this with h2 | h2
    · norm_num at h2
    · exact sub_eq_zero.mp h2
  set y := Complex.exp (a * z) with hy
  have hy0 : y ≠ 0 := Complex.exp_ne_zero _
  have hcosh : Complex.cosh (a * z) = (y + y⁻¹) / 2 := by
    rw [Complex.cosh, hy, Complex.exp_neg]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hceq : (c : ℂ) = ((Real.sqrt 2 : ℝ) + (Real.sqrt 2)⁻¹ : ℝ) / 2 := by
    rw [cosh_half_log_two]
    push_cast
    have : (Real.sqrt 2 : ℝ) ≠ 0 := hs
    field_simp
    have h2' : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by exact_mod_cast h2
    linear_combination (-1 : ℂ) * h2'
  set r : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) with hr
  have hr0 : r ≠ 0 := by rw [hr]; exact_mod_cast hs
  have hyeq : (y + y⁻¹) / 2 = (r + r⁻¹) / 2 := by
    rw [← hcosh, hc, hceq]; rw [hr]; push_cast; ring
  have hq : (y - r) * (y - r⁻¹) = 0 := by
    have h3 : y + y⁻¹ = r + r⁻¹ := by linear_combination 2 * hyeq
    field_simp at h3 ⊢
    linear_combination h3
  have hnorm : ‖y‖ = Real.exp (a * z.re) := by
    rw [hy, Complex.norm_exp]; simp
  have hpos : 0 < a := a_pos
  rcases mul_eq_zero.mp hq with h1 | h1
  · left
    have hyr : y = r := sub_eq_zero.mp h1
    have : Real.exp (a * z.re) = Real.exp (a / 2) := by
      rw [← hnorm, hyr, exp_half_a, hr]; simp
    have := Real.exp_injective this
    nlinarith
  · right
    have hyr : y = r⁻¹ := sub_eq_zero.mp h1
    have : Real.exp (a * z.re) = Real.exp (-(a / 2)) := by
      rw [← hnorm, hyr, Real.exp_neg, exp_half_a, hr]; simp
    have := Real.exp_injective this
    nlinarith

theorem filter_ne_zero_of_off_axis {z : ℂ} (_h0 : 0 < |z.re|) (h1 : |z.re| < 1 / 2) : factor z ≠ 0 := by
  intro h
  rcases filter_zero_iff h with h | h
  · rw [h] at h1; norm_num [abs_of_pos] at h1
  · rw [h] at h1; norm_num at h1

/-- Five-scale coefficients: `4(cosh(az) − c)² = 13/2 − 3√2 (e^{az} + e^{−az}) + (e^{2az} + e^{−2az})`. -/
theorem filter_square_expansion (z : ℂ) :
    (factor z) ^ 2 = 13 / 2 - 3 * Real.sqrt 2 * (Complex.exp (a * z) + Complex.exp (-(a * z))) +
      (Complex.exp (2 * (a * z)) + Complex.exp (-(2 * (a * z)))) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hs : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hcc : (c : ℂ) = 3 / (2 * ((Real.sqrt 2 : ℝ) : ℂ)) := by
    rw [cosh_half_log_two]; push_cast; ring
  have hs' : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have e2 : Complex.exp (2 * (a * z)) = Complex.exp (a * z) ^ 2 := by
    rw [← Complex.exp_nat_mul]; push_cast; ring_nf
  have e2' : Complex.exp (-(2 * (a * z))) = Complex.exp (-(a * z)) ^ 2 := by
    rw [← Complex.exp_nat_mul]; push_cast; ring_nf
  have ee : Complex.exp (a * z) * Complex.exp (-(a * z)) = 1 := by
    rw [← Complex.exp_add]; simp
  unfold factor
  rw [Complex.cosh, hcc, e2, e2']
  set u := Complex.exp (a * z)
  set v := Complex.exp (-(a * z))
  field_simp
  linear_combination (4 * u * v + 6 * u * ((Real.sqrt 2 : ℝ) : ℂ) + 6 * v * ((Real.sqrt 2 : ℝ) : ℂ) - 13) * h2 + 8 * ee

/-- `‖φ‖² = 1 + 1 + (3/√2)² = 13/2` (three boxes of unit norm with disjoint interiors, weights
`1, 1, −3/√2`). -/
theorem norm_sq_filter : (1 : ℝ) ^ 2 + 1 ^ 2 + (3 / Real.sqrt 2) ^ 2 = 13 / 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  rw [div_pow, h2]; norm_num

/-- The `A√x` pole term cancels in the five-scale combination of `T(x)`. -/
theorem pole_cancellation :
    (13 / 2 : ℝ) - 3 * Real.sqrt 2 * (Real.sqrt 2 + (Real.sqrt 2)⁻¹) + (2 + 1 / 2) = 0 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith [h2]

end GppPoleNeutral
