/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.ExplicitFormulaE1Decay

/-!
# Explicit formula, stage E1b: decay of the spectral transform, uniform on the critical strip

For a test function `g` and every `k`,

  `‖s − 1/2‖^k · ‖ĝ(s)‖ ≤ C`   for all `s` with `0 ≤ Re s ≤ 1`   (`spectralTransform_decay_strip`),

with `ĝ(s) = ∫ g(u) e^{(s−1/2)u} du`. E1 has this on each vertical line; the uniform statement is
what the sum over zeros needs, since no zero is assumed to lie on a particular line.

* `spectralTransform_deriv`: `(g')^(s) = −(s − 1/2) ĝ(s)` (integration by parts).
* `spectralTransform_iteratedDeriv`: `(g^{(k)})^(s) = (−(s − 1/2))^k ĝ(s)`.
* `norm_spectralTransform_le`: `‖ĝ(s)‖ ≤ ∫ |g(u)| e^{|u|/2} du` on the strip.

No claim about RH.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.
-/

namespace GppExplicitFormulaE1

open MeasureTheory Complex GppMeyerSpectralWeil
open scoped ContDiff

theorem isTestFunction_deriv {g : ℝ → ℝ} (hg : IsTestFunction g) : IsTestFunction (deriv g) :=
  ⟨(contDiff_infty_iff_deriv.1 hg.1).2, hg.2.deriv⟩

/-- **Integration by parts:** `(g')^(s) = −(s − 1/2) ĝ(s)`. -/
theorem spectralTransform_deriv {g : ℝ → ℝ} (hg : IsTestFunction g) (s : ℂ) :
    spectralTransform (deriv g) s = -(s - 1 / 2) * spectralTransform g s := by
  set c : ℂ := s - 1 / 2 with hc
  set u : ℝ → ℂ := fun x => Complex.exp (c * x) with hu
  set u' : ℝ → ℂ := fun x => c * Complex.exp (c * x) with hu'
  set v : ℝ → ℂ := fun x => (g x : ℂ) with hv
  set v' : ℝ → ℂ := fun x => ((deriv g x : ℝ) : ℂ) with hv'
  have hgd : Differentiable ℝ g := hg.1.differentiable (by simp)
  have hgc : Continuous g := hg.1.continuous
  have hdc : Continuous (deriv g) := (isTestFunction_deriv hg).1.continuous
  have hucont : Continuous u :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hderu : ∀ x : ℝ, HasDerivAt u (u' x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
    have h2 := h1.cexp
    simp only [hu, hu']
    convert h2 using 1
    ring
  have hderv : ∀ x : ℝ, HasDerivAt v (v' x) x := fun x =>
    (hgd x).hasDerivAt.ofReal_comp
  have hvs : HasCompactSupport v := hg.2.comp_left Complex.ofReal_zero
  have hv's : HasCompactSupport v' := hg.2.deriv.comp_left Complex.ofReal_zero
  have hvc : Continuous v := Complex.continuous_ofReal.comp hgc
  have hv'c : Continuous v' := Complex.continuous_ofReal.comp hdc
  have i1 : Integrable (u * v') :=
    (hucont.mul hv'c).integrable_of_hasCompactSupport hv's.mul_left
  have i2 : Integrable (u' * v) :=
    ((continuous_const.mul hucont).mul hvc).integrable_of_hasCompactSupport hvs.mul_left
  have i3 : Integrable (u * v) :=
    (hucont.mul hvc).integrable_of_hasCompactSupport hvs.mul_left
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hderu x) (fun x _ => hderv x) i1 i2 i3
  unfold spectralTransform
  have e1 : ∫ x : ℝ, ((deriv g x : ℝ) : ℂ) * Complex.exp ((s - 1 / 2) * x) = ∫ x : ℝ, u x * v' x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [hu, hv', hc, mul_comm])
  have e2 : ∫ x : ℝ, u' x * v x = c * ∫ x : ℝ, (g x : ℂ) * Complex.exp ((s - 1 / 2) * x) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [hu', hv, hc]; ring)
  rw [e1, key, e2]
  ring

theorem isTestFunction_iterate_deriv {g : ℝ → ℝ} (hg : IsTestFunction g) (k : ℕ) :
    IsTestFunction (deriv^[k] g) := by
  induction k generalizing g with
  | zero => exact hg
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (isTestFunction_deriv hg)

/-- `(g^{(k)})^(s) = (−(s − 1/2))^k ĝ(s)`. -/
theorem spectralTransform_iterate_deriv {g : ℝ → ℝ} (hg : IsTestFunction g) (k : ℕ) (s : ℂ) :
    spectralTransform (deriv^[k] g) s = (-(s - 1 / 2)) ^ k * spectralTransform g s := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (isTestFunction_deriv hg), spectralTransform_deriv hg,
      pow_succ]
    ring

/-- On the closed strip `0 ≤ Re s ≤ 1`, `‖ĥ(s)‖ ≤ ∫ |h(u)| e^{|u|/2} du`. -/
theorem norm_spectralTransform_le {h : ℝ → ℝ} (hh : IsTestFunction h) {s : ℂ}
    (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ‖spectralTransform h s‖ ≤ ∫ u : ℝ, |h u| * Real.exp (|u| / 2) := by
  unfold spectralTransform
  refine (norm_integral_le_integral_norm _).trans ?_
  have hhc : Continuous h := hh.1.continuous
  have hI : Integrable (fun u : ℝ => |h u| * Real.exp (|u| / 2)) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact (hh.2.abs).mul_right
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hI
    (Filter.Eventually.of_forall fun u => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
  have hre : ((s - 1 / 2) * (u : ℂ)).re = (s.re - 1 / 2) * u := by simp
  rw [hre]
  have hb : |s.re - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
    _ = |s.re - 1 / 2| * |u| := abs_mul _ _
    _ ≤ 1 / 2 * |u| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ = |u| / 2 := by ring

/-- **E1b: rapid decay, uniformly on the closed critical strip.** -/
theorem spectralTransform_decay_strip {g : ℝ → ℝ} (hg : IsTestFunction g) (k : ℕ) :
    ∃ C, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → ‖s - 1 / 2‖ ^ k * ‖spectralTransform g s‖ ≤ C := by
  refine ⟨∫ u : ℝ, |deriv^[k] g u| * Real.exp (|u| / 2), fun s h0 h1 => ?_⟩
  have h := norm_spectralTransform_le (isTestFunction_iterate_deriv hg k) h0 h1
  rwa [spectralTransform_iterate_deriv hg, norm_mul, norm_pow, norm_neg] at h

end GppExplicitFormulaE1
