/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import GppVerify.RiemannHypothesis.ExplicitFormulaE1Strip

/-!
# Explicit formula, stage E1c: decay on any vertical strip

Stage E1b gives rapid decay of the spectral transform uniformly on `0 ≤ Re s ≤ 1`. The contour of
the explicit formula needs a wider strip, `-1 ≤ Re s ≤ 2`; the same proof works on
`|Re s - 1/2| ≤ M` for any `M`, with the weight `e^{M |u|}` in place of `e^{|u|/2}`.
-/

open MeasureTheory

namespace GppExplicitFormulaE1

open GppMeyerSpectralWeil

/-- On `|Re s - 1/2| ≤ M`, `‖ĥ(s)‖ ≤ ∫ |h(u)| e^{M |u|} du`. -/
theorem norm_spectralTransform_le_wide {h : ℝ → ℝ} (hh : IsTestFunction h) {M : ℝ} {s : ℂ}
    (hs : |s.re - 1 / 2| ≤ M) :
    ‖spectralTransform h s‖ ≤ ∫ u : ℝ, |h u| * Real.exp (M * |u|) := by
  unfold spectralTransform
  refine (norm_integral_le_integral_norm _).trans ?_
  have hhc : Continuous h := hh.1.continuous
  have hI : Integrable (fun u : ℝ => |h u| * Real.exp (M * |u|)) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact (hh.2.abs).mul_right
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hI
    (Filter.Eventually.of_forall fun u => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
  have hre : ((s - 1 / 2) * (u : ℂ)).re = (s.re - 1 / 2) * u := by simp
  rw [hre]
  calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
    _ = |s.re - 1 / 2| * |u| := abs_mul _ _
    _ ≤ M * |u| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)

/-- **E1c: rapid decay uniformly on `|Re s - 1/2| ≤ M`.** -/
theorem spectralTransform_decay_wide {g : ℝ → ℝ} (hg : IsTestFunction g) (M : ℝ) (k : ℕ) :
    ∃ C, ∀ s : ℂ, |s.re - 1 / 2| ≤ M → ‖s - 1 / 2‖ ^ k * ‖spectralTransform g s‖ ≤ C := by
  refine ⟨∫ u : ℝ, |deriv^[k] g u| * Real.exp (M * |u|), fun s hs => ?_⟩
  have h := norm_spectralTransform_le_wide (isTestFunction_iterate_deriv hg k) hs
  rwa [spectralTransform_iterate_deriv hg, norm_mul, norm_pow, norm_neg] at h

end GppExplicitFormulaE1
