import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The local energy defect of a prime Euler channel and the hyperbolic shadow-paired denominator

Source: Codex, GPPDiscovery2 `research/2026-09-29_prime_euler_julia_colligation.md`, §§4, 6, 9
(the unitary colligation and Blaschke form, §§1–3, are in `LocalEulerShadowColligation` and
`SU11PrimeBlaschke`).

For real `r` and complex `w` with `1 − r w ≠ 0`, let `Θ_r(w) = (w − r)/(1 − r w)`.

* `defect_identity`: `1 − ‖Θ_r(w)‖² = (1 − r²)(1 − ‖w‖²)/‖1 − r w‖²`;
* `theta_lt_one`, `theta_eq_one`, `theta_gt_one`: for `0 < r < 1`, `‖Θ_r(w)‖` is `< 1`, `= 1`, `> 1`
  according as `‖w‖` is `< 1`, `= 1`, `> 1`;
* `norm_w_prime`: for the prime channel `w = p^{1/2 − s}`, `‖w‖ = p^{1/2 − Re s}`, so the three cases are
  `Re s > 1/2`, `= 1/2`, `< 1/2`;
* `shadow_paired_denominator`: with `s = 1/2 + z`,
  `(1 − p^{-s})(1 − p^{-(1−s)}) = 1 + p^{-1} − 2 p^{-1/2} cosh(z log p)`.

## Checks and scope

All claims check. **Not formalized:** the "no-leakage zero theorem" of §8 (a conjectural target, and
the note's falsifier list in §10 is the honest summary of what is missing), the orthogonal direct-integral
decomposition of hidden channels, and the global product formula (§7). A contractive or expansive
visible transfer off the line is consistent with a unitary parent; nothing here locates a zeta zero.
No RH claim.
-/

open Complex

namespace GppLocalEulerDefect

/-- The Blaschke-type transfer `Θ_r(w) = (w − r)/(1 − r w)`. -/
noncomputable def theta (r : ℝ) (w : ℂ) : ℂ := (w - r) / (1 - r * w)

theorem defect_identity (r : ℝ) (w : ℂ) (h : 1 - (r : ℂ) * w ≠ 0) :
    1 - ‖theta r w‖ ^ 2 = (1 - r ^ 2) * (1 - ‖w‖ ^ 2) / ‖1 - (r : ℂ) * w‖ ^ 2 := by
  unfold theta
  have hn : ‖1 - (r : ℂ) * w‖ ≠ 0 := norm_ne_zero_iff.mpr h
  rw [norm_div, div_pow]
  have h1 : ‖(w - r : ℂ)‖ ^ 2 = Complex.normSq (w - r) := Complex.sq_norm _
  have h2 : ‖1 - (r : ℂ) * w‖ ^ 2 = Complex.normSq (1 - (r : ℂ) * w) := Complex.sq_norm _
  have h3 : ‖w‖ ^ 2 = Complex.normSq w := Complex.sq_norm _
  rw [h1, h2, h3]
  have hpos : Complex.normSq (1 - (r : ℂ) * w) ≠ 0 := by
    rw [← h2]; exact pow_ne_zero 2 hn
  have key : Complex.normSq (1 - (r : ℂ) * w) - Complex.normSq (w - r) =
      (1 - r ^ 2) * (1 - Complex.normSq w) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
    ring
  rw [← key, sub_div, div_self hpos]

theorem theta_lt_one (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (w : ℂ) (hw : ‖w‖ < 1) :
    ‖theta r w‖ < 1 := by
  have h : 1 - (r : ℂ) * w ≠ 0 := by
    intro h0
    have : (r : ℂ) * w = 1 := by linear_combination -h0
    have hn := congrArg norm this
    rw [norm_mul, Complex.norm_real, norm_one, Real.norm_eq_abs, abs_of_pos hr0] at hn
    nlinarith [norm_nonneg w]
  have hd := defect_identity r w h
  have hn : 0 < ‖1 - (r : ℂ) * w‖ ^ 2 := by positivity
  have : 0 < 1 - ‖theta r w‖ ^ 2 := by
    rw [hd]; apply div_pos _ hn; apply mul_pos <;> nlinarith [norm_nonneg w]
  nlinarith [norm_nonneg (theta r w)]

theorem theta_eq_one (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (w : ℂ) (hw : ‖w‖ = 1) :
    ‖theta r w‖ = 1 := by
  have h : 1 - (r : ℂ) * w ≠ 0 := by
    intro h0
    have : (r : ℂ) * w = 1 := by linear_combination -h0
    have hn := congrArg norm this
    rw [norm_mul, Complex.norm_real, norm_one, Real.norm_eq_abs, abs_of_pos hr0, hw] at hn
    linarith
  have hd := defect_identity r w h
  rw [hw] at hd
  have : 1 - ‖theta r w‖ ^ 2 = 0 := by rw [hd]; ring
  have h0 := norm_nonneg (theta r w)
  nlinarith

theorem theta_gt_one (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (w : ℂ) (hw : 1 < ‖w‖)
    (h : 1 - (r : ℂ) * w ≠ 0) : 1 < ‖theta r w‖ := by
  have hd := defect_identity r w h
  have hn : 0 < ‖1 - (r : ℂ) * w‖ ^ 2 := by
    have := norm_ne_zero_iff.mpr h
    positivity
  have : 1 - ‖theta r w‖ ^ 2 < 0 := by
    rw [hd]
    apply div_neg_of_neg_of_pos _ hn
    have h1 : 0 < 1 - r ^ 2 := by nlinarith
    have h2 : 1 - ‖w‖ ^ 2 < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg h1 h2
  nlinarith [norm_nonneg (theta r w)]

/-- For the prime channel, `‖p^{1/2 − s}‖ = p^{1/2 − Re s}`. -/
theorem norm_w_prime (p : ℝ) (hp : 0 < p) (s : ℂ) :
    ‖(p : ℂ) ^ ((1 / 2 : ℂ) - s)‖ = p ^ ((1 / 2 : ℝ) - s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp

/-- **Shadow-paired denominator in hyperbolic form.** -/
theorem shadow_paired_denominator (p : ℝ) (hp : 0 < p) (z : ℂ) :
    (1 - (p : ℂ) ^ (-((1 / 2 : ℂ) + z))) * (1 - (p : ℂ) ^ (-(1 - ((1 / 2 : ℂ) + z)))) =
      1 + (p : ℂ)⁻¹ - 2 * (p : ℂ) ^ (-(1 / 2 : ℂ)) * Complex.cosh (z * Real.log p) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hL : (p : ℂ) = Complex.exp (Real.log p) := by
    rw [← Complex.ofReal_exp, Real.exp_log hp]
  have e1 : (p : ℂ) ^ (-((1 / 2 : ℂ) + z)) =
      (p : ℂ) ^ (-(1 / 2 : ℂ)) * Complex.exp (-(z * Real.log p)) := by
    rw [neg_add, Complex.cpow_add _ _ hp', Complex.cpow_def_of_ne_zero hp' (-z)]
    congr 2
    rw [Complex.ofReal_log hp.le]; ring
  have e2 : (p : ℂ) ^ (-(1 - ((1 / 2 : ℂ) + z))) =
      (p : ℂ) ^ (-(1 / 2 : ℂ)) * Complex.exp (z * Real.log p) := by
    have : -(1 - ((1 / 2 : ℂ) + z)) = -(1 / 2 : ℂ) + z := by ring
    rw [this, Complex.cpow_add _ _ hp', Complex.cpow_def_of_ne_zero hp' z]
    congr 2
    rw [Complex.ofReal_log hp.le]; ring
  have e3 : (p : ℂ) ^ (-(1 / 2 : ℂ)) * (p : ℂ) ^ (-(1 / 2 : ℂ)) = (p : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ hp']; norm_num [Complex.cpow_neg_one]
  have e4 : Complex.exp (-(z * Real.log p)) * Complex.exp (z * Real.log p) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [e1, e2, Complex.cosh]
  have : (1 - (p : ℂ) ^ (-(1 / 2 : ℂ)) * Complex.exp (-(z * Real.log p))) *
      (1 - (p : ℂ) ^ (-(1 / 2 : ℂ)) * Complex.exp (z * Real.log p)) =
      1 - (p : ℂ) ^ (-(1 / 2 : ℂ)) * (Complex.exp (-(z * Real.log p)) + Complex.exp (z * Real.log p)) +
        ((p : ℂ) ^ (-(1 / 2 : ℂ)) * (p : ℂ) ^ (-(1 / 2 : ℂ))) *
          (Complex.exp (-(z * Real.log p)) * Complex.exp (z * Real.log p)) := by ring
  rw [this, e3, e4]
  ring

end GppLocalEulerDefect
