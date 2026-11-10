/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import GppVerify.RiemannHypothesis.DigammaGaussSeries

/-!
# Explicit formula, stage E6 (Archimedean term), part 1: Gauss's integral for the digamma function

For `Re z > 0`,

  `ψ(z) = -γ + ∫₀^∞ (e^{-t} - e^{-z t}) / (1 - e^{-t}) dt`.

It is obtained from the Gauss series of stage E2a by writing each `1/(n+1) - 1/(n+1+z)` as
`∫₀^∞ e^{-(n+1)t} (1 - e^{-z t}) dt` and summing under the integral, which is legitimate because
`‖1 - e^{-z t}‖ ≤ ‖z‖ t` makes `∑ₙ ∫ ‖…‖ ≤ ‖z‖ ∑ₙ (n+1)⁻²` finite.
-/

open Complex Set MeasureTheory

namespace GppDigammaIntegral

/-- `‖1 - e^{-w}‖ ≤ ‖w‖` for `Re w ≥ 0`. -/
theorem norm_one_sub_exp_neg_le {w : ℂ} (hw : 0 ≤ w.re) : ‖1 - Complex.exp (-w)‖ ≤ ‖w‖ := by
  have hd : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun u : ℝ => Complex.exp (-(u : ℂ) * w))
      (-w * Complex.exp (-(x : ℂ) * w)) (Icc (0 : ℝ) 1) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => (-(u : ℂ) * w)) (-w) x := by
      have := ((hasDerivAt_id x).ofReal_comp.neg).mul_const w
      simpa using this
    have := h1.cexp
    simpa [mul_comm] using this.hasDerivWithinAt
  have hb : ∀ x ∈ Ico (0 : ℝ) 1, ‖-w * Complex.exp (-(x : ℂ) * w)‖ ≤ ‖w‖ := by
    intro x hx
    rw [norm_mul, norm_neg, Complex.norm_exp]
    have : (-(x : ℂ) * w).re ≤ 0 := by
      simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      nlinarith [hx.1, hw]
    have h2 : Real.exp (-(x : ℂ) * w).re ≤ 1 := Real.exp_le_one_iff.2 this
    calc ‖w‖ * Real.exp (-(x : ℂ) * w).re ≤ ‖w‖ * 1 := by gcongr
      _ = ‖w‖ := mul_one _
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb
  simpa [norm_sub_rev] using this

end GppDigammaIntegral
