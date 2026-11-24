/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import GppVerify.RiemannHypothesis.ExplicitFormulaE1Decay

/-!
# Fourier inversion for the spectral transform on a vertical line

For a test function `g` and a real `σ`, with `Φ(σ + i t) = ∫ g(u) e^{(σ - 1/2 + i t) u} du`,

  `g(v) e^{(σ - 1/2) v} = (1/2π) ∫ e^{-i t v} Φ(σ + i t) dt`.

This is the inversion step used both for the Archimedean term (`σ = 1/2`) and for the prime terms
(`σ = 2`) of the explicit formula.
-/

open Complex Set MeasureTheory FourierTransform SchwartzMap GppMeyerSpectralWeil
open GppExplicitFormulaE1

namespace GppSpectralInversion

/-- The spectral transform on the line `Re s = σ`. -/
noncomputable def line (g : ℝ → ℝ) (σ t : ℝ) : ℂ := spectralTransform g ((σ : ℂ) + t * Complex.I)

theorem line_eq_fourier {g : ℝ → ℝ} (hg : IsTestFunction g) (σ t : ℝ) :
    line g σ t = (𝓕 (shiftedSchwartz hg σ)) (-t / (2 * Real.pi)) :=
  spectralTransform_eq_fourier hg σ t

/-- **Fourier inversion on the line `Re s = σ`.** -/
theorem line_inversion {g : ℝ → ℝ} (hg : IsTestFunction g) (σ v : ℝ) :
    (g v : ℂ) * Complex.exp (((σ : ℂ) - 1 / 2) * v) =
      (1 / (2 * Real.pi) : ℝ) * ∫ t : ℝ, Complex.exp (-(Complex.I * t * v)) * line g σ t := by
  set Gs := shiftedSchwartz hg σ with hGs
  have hshift : ∀ u, Gs u = (g u : ℂ) * Complex.exp (((σ : ℂ) - 1 / 2) * u) := fun u => rfl
  have h1 := congrFun (Gs.continuous.fourierInv_fourier_eq Gs.integrable (𝓕 Gs).integrable) v
  rw [Real.fourierInv_eq_fourier_neg] at h1
  rw [Real.fourier_real_eq_integral_exp_smul] at h1
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hF : ∀ ξ : ℝ, Complex.exp (-(Complex.I * ((-2 * Real.pi * ξ : ℝ) : ℂ) * v)) *
      line g σ (-2 * Real.pi * ξ) =
      Complex.exp (((-2 * Real.pi * ξ * -v : ℝ) : ℂ) * Complex.I) • 𝓕 (⇑Gs) ξ := by
    intro ξ
    rw [line_eq_fourier hg, smul_eq_mul]
    have e : -(-2 * Real.pi * ξ) / (2 * Real.pi) = ξ := by field_simp
    rw [e]
    congr 2
    push_cast
    ring
  have hcomp := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => Complex.exp (-(Complex.I * (t : ℂ) * v)) * line g σ t) (-2 * Real.pi)
  simp only [hF] at hcomp
  rw [h1, hshift] at hcomp
  have habs : |(-2 * Real.pi)⁻¹| = (1 / (2 * Real.pi) : ℝ) := by
    rw [abs_inv, abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos, one_div]
  rw [habs] at hcomp
  rw [hcomp]
  simp only [Complex.real_smul]

end GppSpectralInversion
