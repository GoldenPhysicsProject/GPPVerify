/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.ShiftContour
import GppVerify.RiemannHypothesis.ArchimedeanIdentification
import GppVerify.RiemannHypothesis.ArithmeticReflectionPositivity
import GppVerify.RiemannHypothesis.AutocorrTransport

/-!
# Explicit formula, stage E6e: assembly (even test functions)

For an even test function `g`: the absolutely convergent zero sum equals `weilForm g`.
-/

open Complex Set MeasureTheory GppMeyerSpectralWeil GppLogDerivZeroFree GppXiZeroCounting
  GppXiReflection GppWeilCriterion GppSpectralInversion

namespace GppExplicitFormulaAssembly

/-- `Φ_g(1 - s) = Φ_g(s)` for even `g`. -/
theorem spectralTransform_one_sub_even {g : ℝ → ℝ} (hev : ∀ u, g (-u) = g u) (s : ℂ) :
    spectralTransform g (1 - s) = spectralTransform g s := by
  rw [spectralTransform_one_sub]
  congr 1
  funext u
  exact hev u

/-- On the left line the integrand is minus the right-line one. -/
theorem integral_left_line {g : ℝ → ℝ} (hev : ∀ u, g (-u) = g u) :
    (∫ y : ℝ, logDeriv xi (((-1 : ℝ) : ℂ) + y * Complex.I) *
        spectralTransform g (((-1 : ℝ) : ℂ) + y * Complex.I)) =
      -∫ y : ℝ, logDeriv xi (((2 : ℝ) : ℂ) + y * Complex.I) *
        spectralTransform g (((2 : ℝ) : ℂ) + y * Complex.I) := by
  rw [← integral_neg_eq_self (fun y : ℝ => logDeriv xi (((2 : ℝ) : ℂ) + y * Complex.I) *
        spectralTransform g (((2 : ℝ) : ℂ) + y * Complex.I)), ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h1 : (((2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) = 1 - (((-1 : ℝ) : ℂ) + y * Complex.I) := by
    apply Complex.ext
    · simp; norm_num
    · simp
  simp only []
  rw [h1, logDeriv_xi_one_sub, spectralTransform_one_sub_even hev]
  ring

/-- The zero sum is `(1/π) ∫ (ξ'/ξ) Φ_g (2 + iy) dy` for even `g`. -/
theorem hasSum_even {g : ℝ → ℝ} (hg : IsTestFunction g) (hev : ∀ u, g (-u) = g u) :
    HasSum (fun ρ : nontrivialZeros => (zeroMult ρ : ℂ) * spectralTransform g ρ)
      (((1 / Real.pi : ℝ) : ℂ) * ∫ y : ℝ, logDeriv xi (((2 : ℝ) : ℂ) + y * Complex.I) *
        spectralTransform g (((2 : ℝ) : ℂ) + y * Complex.I)) := by
  have h := GppContourLimit.hasSum_zeroSum_lines hg
  rw [integral_left_line hev] at h
  have key : ∀ J : ℂ, ((1 / Real.pi : ℝ) : ℂ) * J = ((1 / (2 * Real.pi) : ℝ) : ℂ) * (J - -J) := by
    intro J
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    push_cast
    field_simp
    ring
  rw [key]
  exact h


open GppShiftContour

theorem Psi_even {g : ℝ → ℝ} (hev : ∀ u, g (-u) = g u) (s : ℂ) :
    Psi g s = 2 * spectralTransform g s := by
  unfold Psi
  rw [spectralTransform_one_sub_even hev]
  ring

/-- `Φ_g` on the critical line is integrable. -/
theorem integrable_hline {g : ℝ → ℝ} (hg : IsTestFunction g) :
    Integrable fun y : ℝ => spectralTransform g (((1 / 2 : ℝ) : ℂ) + y * Complex.I) := by
  obtain ⟨Cd, hCd⟩ := GppContourLimit.poly_decay hg (3 / 2) 3
  have hcont : Continuous fun y : ℝ => spectralTransform g (((1 / 2 : ℝ) : ℂ) + y * Complex.I) :=
    (GppContourLimit.differentiable_spectralTransform hg).continuous.comp (by fun_prop)
  have hint : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (E := ℝ) (μ := volume) (by simp)
  refine (hint.const_mul |Cd|).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hre : |(((1 / 2 : ℝ) : ℂ) + y * Complex.I).re - 1 / 2| ≤ 3 / 2 := by simp; norm_num
  have hs := hCd _ hre
  have hn : |y| ≤ ‖(((1 / 2 : ℝ) : ℂ) + y * Complex.I) - 1 / 2‖ := by
    have h := Complex.abs_im_le_norm ((((1 / 2 : ℝ) : ℂ) + y * Complex.I) - 1 / 2)
    have e : ((((1 / 2 : ℝ) : ℂ) + y * Complex.I) - 1 / 2).im = y := by simp
    rwa [e] at h
  have hp : (1 + |y|) ^ 3 ≤ (1 + ‖(((1 / 2 : ℝ) : ℂ) + y * Complex.I) - 1 / 2‖) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  set P := ‖spectralTransform g (((1 / 2 : ℝ) : ℂ) + y * Complex.I)‖ with hP
  have hP0 : 0 ≤ P := norm_nonneg _
  have hy0 : 0 < 1 + |y| := by positivity
  have hPb : (1 + |y|) ^ 3 * P ≤ |Cd| :=
    (mul_le_mul_of_nonneg_right hp hP0).trans (hs.trans (le_abs_self _))
  have hrp : (1 + ‖y‖) ^ (-(2 : ℝ)) = ((1 + |y|) ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, Real.rpow_neg hy0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  rw [hrp]
  have hP' : P ≤ |Cd| / (1 + |y|) ^ 3 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc P ≤ |Cd| / (1 + |y|) ^ 3 := hP'
    _ ≤ |Cd| * ((1 + |y|) ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply inv_anti₀ (by positivity)
        nlinarith [pow_pos hy0 2, abs_nonneg y]

/-- The Fourier inversion at `0`: `(1/2π) ∫ Φ_g(1/2 + iy) dy = g(0)`. -/
theorem integral_hline {g : ℝ → ℝ} (hg : IsTestFunction g) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ y : ℝ, spectralTransform g (((1 / 2 : ℝ) : ℂ) + y * Complex.I) = (g 0 : ℂ) := by
  have h := line_inversion hg (1 / 2) 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, neg_zero] at h
  rw [h]
  simp only [one_mul]
  rfl


/-- The critical-line point `1/2 + i y`. -/
noncomputable def sh (y : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + y * Complex.I

theorem sh_ne_zero (y : ℝ) : sh y ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp [sh] at this

theorem sh_sub_one_ne_zero (y : ℝ) : sh y - 1 ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp [sh] at this; norm_num at this

theorem hline_even {g : ℝ → ℝ} (hev : ∀ u, g (-u) = g u) (y : ℝ) :
    spectralTransform g (sh (-y)) = spectralTransform g (sh y) := by
  have : sh (-y) = 1 - sh y := by
    unfold sh; apply Complex.ext <;> (simp; try norm_num)
  rw [this, spectralTransform_one_sub_even hev]

/-- The odd part of `H` on the critical line. -/
noncomputable def Odd' (g : ℝ → ℝ) (y : ℝ) : ℂ :=
  (1 / (sh y - 1) + 1 / sh y) * (2 * spectralTransform g (sh y))

/-- The remaining part of `H` on the critical line. -/
noncomputable def Rest' (g : ℝ → ℝ) (y : ℝ) : ℂ :=
  (-(Real.log Real.pi : ℂ) + Complex.digamma (sh y / 2)) * spectralTransform g (sh y)

theorem H_half_eq {g : ℝ → ℝ} (hev : ∀ u, g (-u) = g u) (y : ℝ) :
    H g (sh y) = Odd' g y + Rest' g y := by
  unfold H R0 Odd' Rest'
  rw [Psi_even hev]
  ring

theorem Odd'_neg {g : ℝ → ℝ} (hev : ∀ u, g (-u) = g u) (y : ℝ) : Odd' g (-y) = -Odd' g y := by
  unfold Odd'
  rw [hline_even hev]
  have h1 : sh (-y) - 1 = -sh y := by unfold sh; apply Complex.ext <;> (simp; try norm_num)
  have h2 : sh (-y) = -(sh y - 1) := by unfold sh; apply Complex.ext <;> (simp; try norm_num)
  rw [h1, h2, one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div]
  ring

theorem integrable_Odd' {g : ℝ → ℝ} (hg : IsTestFunction g) : Integrable (Odd' g) := by
  have hcont : Continuous (Odd' g) := by
    unfold Odd'
    have hsh : Continuous sh := by unfold sh; fun_prop
    refine Continuous.mul (Continuous.add ?_ ?_) ?_
    · exact continuous_const.div (hsh.sub continuous_const) sh_sub_one_ne_zero
    · exact continuous_const.div hsh sh_ne_zero
    · exact continuous_const.mul
        ((GppContourLimit.differentiable_spectralTransform hg).continuous.comp hsh)
  have hI := (integrable_hline hg).norm.const_mul 8
  refine hI.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  unfold Odd'
  rw [norm_mul]
  have hs0 : 1 / 2 ≤ ‖sh y‖ := by
    have := Complex.abs_re_le_norm (sh y)
    simp [sh] at this
    simpa [sh] using this
  have hs1 : 1 / 2 ≤ ‖sh y - 1‖ := by
    have := Complex.abs_re_le_norm (sh y - 1)
    have e : (sh y - 1).re = -(1 / 2) := by simp [sh]; norm_num
    rw [e] at this
    simpa using this
  have e1 : ‖1 / (sh y - 1)‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
  have e2 : ‖1 / sh y‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
  have e3 : ‖(2 : ℂ) * spectralTransform g (sh y)‖ = 2 * ‖spectralTransform g (sh y)‖ := by
    rw [norm_mul]; simp
  have hn := norm_add_le (1 / (sh y - 1)) (1 / sh y)
  have hnn : 0 ≤ ‖spectralTransform g (sh y)‖ := norm_nonneg _
  have hh : ‖spectralTransform g (((1 / 2 : ℝ) : ℂ) + y * Complex.I)‖ = ‖spectralTransform g (sh y)‖ := rfl
  rw [e3]
  calc ‖1 / (sh y - 1) + 1 / sh y‖ * (2 * ‖spectralTransform g (sh y)‖)
      ≤ 4 * (2 * ‖spectralTransform g (sh y)‖) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 8 * ‖spectralTransform g (sh y)‖ := by ring

theorem integral_Odd' {g : ℝ → ℝ} (hev : ∀ u, g (-u) = g u) : ∫ y : ℝ, Odd' g y = 0 := by
  have h : ∫ y : ℝ, Odd' g y = -∫ y : ℝ, Odd' g y := by
    conv_lhs => rw [← integral_neg_eq_self (fun y : ℝ => Odd' g y)]
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => Odd'_neg hev y)
  linear_combination (1 / 2 : ℂ) * h


/-- **The critical line gives the archimedean term:**
`(1/2π) ∫ H(1/2 + iy) dy = archimedeanTerm g` for even `g`. -/
theorem half_line {g : ℝ → ℝ} (hg : IsTestFunction g) (hev : ∀ u, g (-u) = g u) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, H g (sh y) =
      ((GppArchimedeanFloor.archimedeanTerm g : ℝ) : ℂ) := by
  have hHint : Integrable fun y : ℝ => H g (sh y) :=
    integrable_H_line hg (σ := 1 / 2) (Or.inl rfl)
  have hRest : Integrable (Rest' g) := by
    have : Rest' g = fun y => H g (sh y) - Odd' g y := by
      funext y; rw [H_half_eq hev]; ring
    rw [this]; exact hHint.sub (integrable_Odd' hg)
  have hhl : Integrable fun y : ℝ => spectralTransform g (sh y) := integrable_hline hg
  have hψ : Integrable fun y : ℝ => spectralTransform g (sh y) *
      Complex.digamma (sh y / 2) := by
    have : (fun y : ℝ => spectralTransform g (sh y) * Complex.digamma (sh y / 2)) =
        fun y => Rest' g y + (Real.log Real.pi : ℂ) * spectralTransform g (sh y) := by
      funext y; unfold Rest'; ring
    rw [this]; exact hRest.add (hhl.const_mul _)
  have hsplit : ∫ y : ℝ, H g (sh y) = ∫ y : ℝ, Rest' g y := by
    have : (fun y : ℝ => H g (sh y)) = fun y => Odd' g y + Rest' g y := by
      funext y; exact H_half_eq hev y
    rw [this, integral_add (integrable_Odd' hg) hRest, integral_Odd' hev, zero_add]
  have hRest_eq : ∫ y : ℝ, Rest' g y = -(Real.log Real.pi : ℂ) * (∫ y : ℝ, spectralTransform g (sh y)) +
      (∫ y : ℝ, spectralTransform g (sh y) * Complex.digamma (sh y / 2)) := by
    have : Rest' g = fun y => (-(Real.log Real.pi : ℂ)) * spectralTransform g (sh y) +
        spectralTransform g (sh y) * Complex.digamma (sh y / 2) := by
      funext y; unfold Rest'; ring
    rw [this, integral_add (hhl.const_mul _) hψ, integral_const_mul]
  have hid := GppArchimedeanId.archimedean_identification hg
  have hid2 : ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, spectralTransform g (sh y) *
        Complex.digamma (sh y / 2) =
      ((GppArchimedeanFloor.archimedeanTerm g + g 0 * Real.log Real.pi : ℝ) : ℂ) := by
    rw [← hid]
    congr 2
    funext y
    unfold GppArchimedeanId.hline sh
    congr 2
    · push_cast; ring_nf
    · push_cast; ring_nf
  have hinv := integral_hline hg
  rw [hsplit, hRest_eq, mul_add]
  have e1 : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (-(Real.log Real.pi : ℂ) * (∫ y : ℝ, spectralTransform g (sh y))) =
      -(Real.log Real.pi : ℂ) * (g 0 : ℂ) := by
    rw [← hinv]; unfold sh; ring
  rw [e1, hid2]
  push_cast
  ring

end GppExplicitFormulaAssembly
