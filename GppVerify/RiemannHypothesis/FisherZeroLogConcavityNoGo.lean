import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Positivity and strong log-concavity do not confine Fisher zeros

Source: Codex, GPPDiscovery2 branch `codex/discovery-workbench`,
`research/2026-09-27_xi_vacuum_survival_fisher_zero_nogo.md` §§3–4 (commit `215fdc0`);
formalized here 2026-09-28.

The note writes `ξ(1/2 + it)/ξ(1/2)` as the characteristic function `⟨Ω, e^{itH} Ω⟩` of a positive
spectral density, so RH says its complex-time ("Fisher") zeros are all real. It then kills the
naive closure "positive spectral density ⟹ real Fisher zeros", even with arbitrarily strong
log-concavity, by an explicit counterexample. This file formalizes that counterexample.

For `A > 0`, `b > 0`, `0 < ε < 1`, let `q(x) = e^{-A x²/2} (1 + ε cos(b x))`.

* `density_pos`: `q > 0` everywhere;
* `charFun_eq`: for every complex `t`,
  `∫ e^{itx} q(x) dx = √(2π/A) e^{-t²/(2A)} (1 + ε e^{-b²/(2A)} cosh(bt/A))`;
* `charFun_zero`: at `t₀ = (A/b)(log(C₀ + √(C₀² - 1)) + iπ)` with `C₀ = e^{b²/(2A)}/ε > 1`, the
  characteristic function vanishes, and `t₀` is neither real nor purely imaginary;
* `logDensity_second_deriv_le`: `(log q)'' = -A - εb²(cos bx + ε)/(1 + ε cos bx)²
  ≤ -A + εb²/(1-ε)`, so taking `A` large makes `q` as strongly log-concave as desired while the
  off-axis zero persists.

Every step was re-derived by hand before formalizing; the note's formulas, including the
numerical example `A = 12, ε = 0.1, b = 1` (curvature `≤ -11.889`, first zero
`≈ ±36.421 + 37.699 i`), are correct.

## Scope

This is a no-go for one proof strategy. It says nothing about the actual BPY density; the
note's §1 identity `ξ(1/2+it)/ξ(1/2) = ⟨Ω, e^{itH}Ω⟩` is not formalized here, and nothing in this
file bears on RH beyond ruling the naive route out.
-/

open Complex MeasureTheory Real

namespace GppFisherZeroNoGo

/-- The counterexample density `q(x) = e^{-A x²/2} (1 + ε cos(bx))`. -/
noncomputable def density (A ε b x : ℝ) : ℝ := Real.exp (-A * x ^ 2 / 2) * (1 + ε * Real.cos (b * x))

theorem density_pos (A ε b : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (x : ℝ) : 0 < density A ε b x := by
  unfold density
  have : -1 ≤ Real.cos (b * x) := Real.neg_one_le_cos _
  have : 0 < 1 + ε * Real.cos (b * x) := by nlinarith
  positivity

/-- The (complexified) characteristic function `∫ e^{itx} q(x) dx`. -/
noncomputable def charFun (A ε b : ℝ) (t : ℂ) : ℂ :=
  ∫ x : ℝ, cexp (I * t * x) * (density A ε b x : ℂ)

lemma gauss (A : ℝ) (hA : 0 < A) (c : ℂ) :
    ∫ x : ℝ, cexp (-(A / 2 : ℂ) * x ^ 2 + c * x + 0) =
      ((π : ℂ) / (A / 2)) ^ (1 / 2 : ℂ) * cexp (c ^ 2 / (2 * A)) := by
  have hb : (-(A / 2 : ℂ)).re < 0 := by simp; linarith
  rw [integral_cexp_quadratic hb c 0]
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  congr 2
  · ring
  · field_simp; ring

/-- **Closed form.** `∫ e^{itx} q = √(2π/A) e^{-t²/(2A)} (1 + ε e^{-b²/(2A)} cosh(bt/A))`. -/
theorem charFun_eq (A ε b : ℝ) (hA : 0 < A) (t : ℂ) :
    charFun A ε b t = ((π : ℂ) / (A / 2)) ^ (1 / 2 : ℂ) * cexp (-t ^ 2 / (2 * A)) *
      (1 + ε * cexp (-(b : ℂ) ^ 2 / (2 * A)) * Complex.cosh (b * t / A)) := by
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hpt : ∀ x : ℝ, cexp (I * t * x) * (density A ε b x : ℂ) =
      cexp (-(A / 2 : ℂ) * x ^ 2 + (I * t) * x + 0) +
        (ε / 2 : ℂ) * cexp (-(A / 2 : ℂ) * x ^ 2 + (I * (t + b)) * x + 0) +
        (ε / 2 : ℂ) * cexp (-(A / 2 : ℂ) * x ^ 2 + (I * (t - b)) * x + 0) := by
    intro x
    unfold density
    push_cast
    have f0 : cexp (-(A / 2 : ℂ) * x ^ 2 + (I * t) * x + 0) =
        cexp (I * t * x) * cexp (-A * x ^ 2 / 2) := by
      rw [← Complex.exp_add]; ring_nf
    have f1 : cexp (-(A / 2 : ℂ) * x ^ 2 + (I * (t + b)) * x + 0) =
        cexp (I * t * x) * cexp (-A * x ^ 2 / 2) * cexp (b * x * I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
    have f2 : cexp (-(A / 2 : ℂ) * x ^ 2 + (I * (t - b)) * x + 0) =
        cexp (I * t * x) * cexp (-A * x ^ 2 / 2) * cexp (-(b * x) * I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
    rw [f0, f1, f2, Complex.cos]
    ring
  have i0 := integrable_cexp_quadratic' (b := -(A / 2 : ℂ)) (by simp; linarith) (I * t) 0
  have i1 := integrable_cexp_quadratic' (b := -(A / 2 : ℂ)) (by simp; linarith) (I * (t + b)) 0
  have i2 := integrable_cexp_quadratic' (b := -(A / 2 : ℂ)) (by simp; linarith) (I * (t - b)) 0
  unfold charFun
  simp_rw [hpt]
  have h01 : Integrable (fun x : ℝ => cexp (-(A / 2 : ℂ) * x ^ 2 + (I * t) * x + 0) +
      (ε / 2 : ℂ) * cexp (-(A / 2 : ℂ) * x ^ 2 + (I * (t + b)) * x + 0)) :=
    i0.add (i1.const_mul _)
  rw [integral_add h01 (i2.const_mul _), integral_add i0 (i1.const_mul _),
    integral_const_mul, integral_const_mul, gauss A hA, gauss A hA, gauss A hA]
  rw [Complex.cosh]
  have ex : ∀ u v : ℂ, cexp u * cexp v = cexp (u + v) := fun u v => (Complex.exp_add u v).symm
  have k1 : cexp ((I * (t + b)) ^ 2 / (2 * A)) =
      cexp (-t ^ 2 / (2 * A)) * (cexp (-(b : ℂ) ^ 2 / (2 * A)) * cexp (-(b * t / A))) := by
    rw [ex, ex]; congr 1; field_simp; ring_nf; rw [Complex.I_sq]; ring
  have k2 : cexp ((I * (t - b)) ^ 2 / (2 * A)) =
      cexp (-t ^ 2 / (2 * A)) * (cexp (-(b : ℂ) ^ 2 / (2 * A)) * cexp (b * t / A)) := by
    rw [ex, ex]; congr 1; field_simp; ring_nf; rw [Complex.I_sq]; ring
  have k0 : cexp ((I * t) ^ 2 / (2 * A)) = cexp (-t ^ 2 / (2 * A)) := by
    congr 1; ring_nf; rw [Complex.I_sq]; ring
  rw [k0, k1, k2]
  ring

lemma cosh_add_pi_I (w : ℂ) : Complex.cosh (w + π * I) = -Complex.cosh w := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_pi, Complex.sin_pi]
  ring

lemma real_cosh_log (C : ℝ) (hC : 1 ≤ C) :
    Real.cosh (Real.log (C + Real.sqrt (C ^ 2 - 1))) = C := by
  have hs : 0 ≤ C ^ 2 - 1 := by nlinarith
  have hy : 0 < C + Real.sqrt (C ^ 2 - 1) := by positivity
  have hprod : (C + Real.sqrt (C ^ 2 - 1)) * (C - Real.sqrt (C ^ 2 - 1)) = 1 := by
    have := Real.sq_sqrt hs; nlinarith
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_log hy]
  have hinv : (C + Real.sqrt (C ^ 2 - 1))⁻¹ = C - Real.sqrt (C ^ 2 - 1) := by
    exact inv_eq_of_mul_eq_one_right hprod
  rw [hinv]; ring

/-- **Explicit off-axis Fisher zero.** With `C₀ = e^{b²/(2A)}/ε > 1`,
`w = log(C₀ + √(C₀² - 1)) > 0` and `t₀ = (A/b)(w + iπ)`, the characteristic function of the
positive density `q` vanishes at `t₀`, and `t₀` is neither real nor purely imaginary. -/
theorem charFun_zero (A ε b : ℝ) (hA : 0 < A) (hb : 0 < b) (hε0 : 0 < ε) (hε1 : ε < 1) :
    let C₀ := Real.exp (b ^ 2 / (2 * A)) / ε
    let w := Real.log (C₀ + Real.sqrt (C₀ ^ 2 - 1))
    let t₀ : ℂ := (A / b : ℝ) * ((w : ℂ) + π * I)
    charFun A ε b t₀ = 0 ∧ t₀.im ≠ 0 ∧ t₀.re ≠ 0 := by
  intro C₀ w t₀
  have hC : 1 < C₀ := by
    have : 1 ≤ Real.exp (b ^ 2 / (2 * A)) := Real.one_le_exp (by positivity)
    rw [lt_div_iff₀ hε0]; linarith
  have hw : 0 < w := by
    apply Real.log_pos
    have : 0 ≤ Real.sqrt (C₀ ^ 2 - 1) := Real.sqrt_nonneg _
    linarith
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [charFun_eq A ε b hA]
    have harg : (b : ℂ) * t₀ / A = (w : ℂ) + π * I := by
      simp only [t₀]; push_cast; field_simp
    rw [harg, cosh_add_pi_I, ← Complex.ofReal_cosh, real_cosh_log C₀ hC.le]
    have hkey : (1 : ℂ) + ε * cexp (-(b : ℂ) ^ 2 / (2 * A)) * -(C₀ : ℂ) = 0 := by
      simp only [C₀]
      push_cast
      have he : cexp (-(b : ℂ) ^ 2 / (2 * A)) * cexp ((b : ℂ) ^ 2 / (2 * A)) = 1 := by
        rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
      have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε0.ne'
      simp only [neg_div] at he ⊢
      field_simp
      linear_combination -he
    rw [hkey, mul_zero]
  · simp only [t₀]
    simp [hA.ne', hb.ne', Real.pi_ne_zero]
  · simp only [t₀]
    simp [hA.ne', hb.ne', hw.ne']

/-- `(log q)'` for the counterexample density. -/
noncomputable def logDeriv1 (A ε b x : ℝ) : ℝ :=
  -A * x - ε * b * Real.sin (b * x) / (1 + ε * Real.cos (b * x))

/-- `(log q)''` for the counterexample density. -/
noncomputable def logDeriv2 (A ε b x : ℝ) : ℝ :=
  -A - ε * b ^ 2 * (Real.cos (b * x) + ε) / (1 + ε * Real.cos (b * x)) ^ 2

lemma one_add_pos (ε b x : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) : 0 < 1 + ε * Real.cos (b * x) := by
  have : -1 ≤ Real.cos (b * x) := Real.neg_one_le_cos _
  nlinarith

theorem hasDerivAt_log_density (A ε b : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (x : ℝ) :
    HasDerivAt (fun x => Real.log (density A ε b x)) (logDeriv1 A ε b x) x := by
  have hpos := one_add_pos ε b x hε0 hε1
  have hsplit : (fun x => Real.log (density A ε b x)) =
      fun x => -A * x ^ 2 / 2 + Real.log (1 + ε * Real.cos (b * x)) := by
    funext y
    unfold density
    rw [Real.log_mul (Real.exp_pos _).ne' (one_add_pos ε b y hε0 hε1).ne', Real.log_exp]
  rw [hsplit]
  have h1 : HasDerivAt (fun x : ℝ => -A * x ^ 2 / 2) (-A * x) x := by
    have := ((hasDerivAt_pow 2 x).const_mul (-A)).div_const 2
    refine this.congr_deriv ?_; push_cast; ring
  have hc : HasDerivAt (fun x : ℝ => 1 + ε * Real.cos (b * x))
      (ε * (-Real.sin (b * x) * b)) x := by
    have := (((hasDerivAt_id x).const_mul b).cos).const_mul ε
    have := this.const_add 1
    refine this.congr_deriv ?_; simp
  have h2 := hc.log hpos.ne'
  have := h1.add h2
  refine this.congr_deriv ?_
  unfold logDeriv1
  field_simp
  ring

theorem hasDerivAt_logDeriv1 (A ε b : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (x : ℝ) :
    HasDerivAt (logDeriv1 A ε b) (logDeriv2 A ε b x) x := by
  have hpos := one_add_pos ε b x hε0 hε1
  have hs : HasDerivAt (fun x : ℝ => ε * b * Real.sin (b * x))
      (ε * b * (Real.cos (b * x) * b)) x := by
    have := (((hasDerivAt_id x).const_mul b).sin).const_mul (ε * b)
    refine this.congr_deriv ?_; simp
  have hc : HasDerivAt (fun x : ℝ => 1 + ε * Real.cos (b * x))
      (ε * (-Real.sin (b * x) * b)) x := by
    have := (((hasDerivAt_id x).const_mul b).cos).const_mul ε
    have := this.const_add 1
    refine this.congr_deriv ?_; simp
  have hq := hs.div hc hpos.ne'
  have hl : HasDerivAt (fun x : ℝ => -A * x) (-A) x := by
    have := (hasDerivAt_id x).const_mul (-A)
    refine this.congr_deriv ?_; simp
  have := hl.sub hq
  unfold logDeriv1
  refine this.congr_deriv ?_
  unfold logDeriv2
  have hsc := Real.sin_sq_add_cos_sq (b * x)
  field_simp
  linear_combination (-(ε ^ 2 * b ^ 2)) * hsc

/-- **Uniform strong log-concavity.** `(log q)'' ≤ -A + εb²/(1-ε)` everywhere. -/
theorem logDeriv2_le (A ε b : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (x : ℝ) :
    logDeriv2 A ε b x ≤ -A + ε * b ^ 2 / (1 - ε) := by
  unfold logDeriv2
  have hpos := one_add_pos ε b x hε0 hε1
  have hc1 : -1 ≤ Real.cos (b * x) := Real.neg_one_le_cos _
  have hc2 : Real.cos (b * x) ≤ 1 := Real.cos_le_one _
  have h1e : 0 < 1 - ε := by linarith
  -- `-(c + ε)/(1 + εc)² ≤ 1/(1 - ε)` for `c ∈ [-1, 1]`
  have key : -(Real.cos (b * x) + ε) / (1 + ε * Real.cos (b * x)) ^ 2 ≤ 1 / (1 - ε) := by
    rw [div_le_div_iff₀ (by positivity) h1e]
    set c := Real.cos (b * x)
    nlinarith [mul_nonneg hε0 (by linarith : (0 : ℝ) ≤ c + 1), mul_nonneg hε0 hε0,
      mul_nonneg (mul_nonneg hε0 hε0) (by linarith : (0 : ℝ) ≤ c + 1),
      mul_nonneg hε0 (mul_nonneg (by linarith : (0 : ℝ) ≤ c + 1) (by linarith : (0 : ℝ) ≤ 1 - c))]
  have hb2 : 0 ≤ ε * b ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left key hb2
  have e1 : ε * b ^ 2 * (-(Real.cos (b * x) + ε) / (1 + ε * Real.cos (b * x)) ^ 2) =
      -(ε * b ^ 2 * (Real.cos (b * x) + ε) / (1 + ε * Real.cos (b * x)) ^ 2) := by ring
  have e2 : ε * b ^ 2 * (1 / (1 - ε)) = ε * b ^ 2 / (1 - ε) := by ring
  rw [e1, e2] at this
  linarith

end GppFisherZeroNoGo
