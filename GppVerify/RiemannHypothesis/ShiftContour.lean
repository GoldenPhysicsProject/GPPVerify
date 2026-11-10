/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.ContourLimit

/-!
# Explicit formula, stage E6e (shift): from `Re s = 2` to `Re s = 1/2`

For a test function `g` put `Ψ(s) = Φ_g(s) + Φ_g(1 - s)` (entire) and
`H(s) = Ψ(s)/(s - 1) + R₀(s) Ψ(s)`, `R₀(s) = 1/s - (log π)/2 + ψ(s/2)/2`. Then

  `∫ H(2 + iy) dy - ∫ H(1/2 + iy) dy = 2π Ψ(1)`

(residue at `s = 1`; the rest is holomorphic on `Re s > 0`).
-/

open Complex Set MeasureTheory Metric Filter Topology GppMeyerSpectralWeil
open scoped Interval Topology

namespace GppShiftContour

/-- `Ψ_g(s) = Φ_g(s) + Φ_g(1 - s)`. -/
noncomputable def Psi (g : ℝ → ℝ) (s : ℂ) : ℂ := spectralTransform g s + spectralTransform g (1 - s)

/-- `R₀(s) = 1/s - (log π)/2 + ψ(s/2)/2`. -/
noncomputable def R0 (s : ℂ) : ℂ :=
  1 / s + (-(Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2)

/-- The shifted integrand. -/
noncomputable def H (g : ℝ → ℝ) (s : ℂ) : ℂ := Psi g s / (s - 1) + R0 s * Psi g s

theorem differentiable_Psi {g : ℝ → ℝ} (hg : IsTestFunction g) : Differentiable ℂ (Psi g) :=
  (GppContourLimit.differentiable_spectralTransform hg).add
    ((GppContourLimit.differentiable_spectralTransform hg).comp
      ((differentiable_const (1 : ℂ)).sub differentiable_id))

/-- `ψ(s/2)` is continuous on `Re s > 0`. -/
theorem continuousAt_R0 {s : ℂ} (hs : 0 < s.re) : ContinuousAt R0 s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have h1 : ContinuousAt (fun s : ℂ => 1 / s) s := continuousAt_const.div continuousAt_id hs0
  have h2 : ContinuousAt (fun s : ℂ => Complex.digamma (s / 2)) s :=
    (GppXiLineBounds.continuousAt_digamma (by simpa using hs)).comp
      (continuousAt_id.div_const 2)
  exact h1.add (continuousAt_const.add (h2.div_const 2))

theorem differentiableAt_R0 {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ R0 s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : AnalyticAt ℂ Complex.Gamma (s / 2) := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have : ∀ᶠ w in 𝓝 (s / 2), 0 < w.re := hopen.mem_nhds (by simpa using hs)
    filter_upwards [this] with w hw
    refine Complex.differentiableAt_Gamma w (fun m h => ?_)
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hdig : AnalyticAt ℂ Complex.digamma (s / 2) := by
    have h : Complex.digamma = fun w => deriv Complex.Gamma w / Complex.Gamma w := by
      funext w; rw [Complex.digamma_def, logDeriv_apply]
    rw [h]
    exact hG.deriv.div hG (Complex.Gamma_ne_zero hne)
  have h2 : DifferentiableAt ℂ (fun s : ℂ => Complex.digamma (s / 2)) s :=
    hdig.differentiableAt.comp s (differentiableAt_id.div_const 2)
  exact (differentiableAt_const (1 : ℂ)).div differentiableAt_id hs0 |>.add
    (differentiableAt_const _ |>.add (h2.div_const 2))

/-- Uniform linear growth of `ψ(s/2)` on the strip `1/2 ≤ Re s ≤ 2`. -/
theorem norm_digamma_strip_le :
    ∃ C : ℝ, ∀ σ y : ℝ, σ ∈ Icc (1 / 2 : ℝ) 2 →
      ‖Complex.digamma (((σ : ℂ) + y * Complex.I) / 2)‖ ≤ C * (1 + |y|) := by
  obtain ⟨C1, hC1⟩ := GppDigammaVertical.norm_digamma_le 1 (by norm_num)
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Complex.digamma ((((p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) / 2))
      (Icc (1 / 2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) := by
    intro p hp
    have hre : 0 < ((((p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) / 2).re := by
      simp; linarith [hp.1.1]
    have hlin : Continuous fun p : ℝ × ℝ => (((p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) / 2 := by
      fun_prop
    exact ((GppXiLineBounds.continuousAt_digamma hre).comp
      (f := fun p : ℝ × ℝ => (((p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) / 2)
      hlin.continuousAt).continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨|B| + |C1|, fun σ y hσ => ?_⟩
  have hB0 : 0 ≤ |B| := abs_nonneg _
  have hC0 : 0 ≤ |C1| := abs_nonneg _
  rcases le_or_gt 2 |y| with hy | hy
  · have him : 1 ≤ |((((σ : ℝ) : ℂ) + (y : ℂ) * Complex.I) / 2).im| := by
      simp; rw [abs_div, abs_two]; linarith
    have hre : |((((σ : ℝ) : ℂ) + (y : ℂ) * Complex.I) / 2).re| ≤ 1 := by
      simp; rw [abs_of_nonneg (by linarith [hσ.1])]; linarith [hσ.2]
    have h := hC1 _ hre him
    have himabs : |((((σ : ℝ) : ℂ) + (y : ℂ) * Complex.I) / 2).im| = |y| / 2 := by
      simp [abs_div]
    rw [himabs] at h
    have hlog : Real.log (|y| / 2 + 1) ≤ |y| / 2 := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < |y| / 2 + 1)
      linarith
    have : C1 * Real.log (|y| / 2 + 1) ≤ |C1| * (|y| / 2) :=
      calc C1 * Real.log (|y| / 2 + 1) ≤ |C1| * Real.log (|y| / 2 + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.log_nonneg (by linarith [abs_nonneg y]))
        _ ≤ |C1| * (|y| / 2) := mul_le_mul_of_nonneg_left hlog hC0
    nlinarith [abs_nonneg y]
  · have := hB (σ, y) ⟨hσ, ⟨by linarith [(abs_lt.1 hy).1], by linarith [(abs_lt.1 hy).2]⟩⟩
    have hnn : 0 ≤ |y| := abs_nonneg y
    nlinarith [le_abs_self B]


/-- Decay of `Ψ` on the strip `1/2 ≤ Re s ≤ 2`, in terms of `Im s`. -/
theorem norm_Psi_le {g : ℝ → ℝ} (hg : IsTestFunction g) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → (1 + |s.im|) ^ 3 * ‖Psi g s‖ ≤ C := by
  obtain ⟨Cd, hCd⟩ := GppContourLimit.poly_decay hg (3 / 2) 3
  refine ⟨2 * |Cd|, fun s h1 h2 => ?_⟩
  have hn : |s.im| ≤ ‖s - 1 / 2‖ := by
    have h := Complex.abs_im_le_norm (s - 1 / 2)
    have e : (s - 1 / 2).im = s.im := by simp
    rwa [e] at h
  have hp : (1 + |s.im|) ^ 3 ≤ (1 + ‖s - 1 / 2‖) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have a1 := hCd s (by rw [abs_le]; constructor <;> linarith)
  have a2 := hCd (1 - s) (by
    have : (1 - s).re = 1 - s.re := by simp
    rw [this, abs_le]; constructor <;> linarith)
  have hn2 : ‖(1 - s) - 1 / 2‖ = ‖s - 1 / 2‖ := by
    rw [show (1 - s) - 1 / 2 = -(s - 1 / 2) by ring, norm_neg]
  rw [hn2] at a2
  unfold Psi
  have hq : 0 ≤ (1 + |s.im|) ^ 3 := by positivity
  calc (1 + |s.im|) ^ 3 * ‖spectralTransform g s + spectralTransform g (1 - s)‖
      ≤ (1 + |s.im|) ^ 3 * (‖spectralTransform g s‖ + ‖spectralTransform g (1 - s)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hq
    _ = (1 + |s.im|) ^ 3 * ‖spectralTransform g s‖ + (1 + |s.im|) ^ 3 * ‖spectralTransform g (1 - s)‖ := by
        ring
    _ ≤ (1 + ‖s - 1 / 2‖) ^ 3 * ‖spectralTransform g s‖ +
          (1 + ‖s - 1 / 2‖) ^ 3 * ‖spectralTransform g (1 - s)‖ :=
        add_le_add (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
    _ ≤ |Cd| + |Cd| := add_le_add (a1.trans (le_abs_self _)) (a2.trans (le_abs_self _))
    _ = 2 * |Cd| := by ring

/-- **Decay of `H`** on the strip `1/2 ≤ Re s ≤ 2` away from the pole `s = 1`. -/
theorem norm_H_le {g : ℝ → ℝ} (hg : IsTestFunction g) :
    ∃ K : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → 1 / 2 ≤ ‖s - 1‖ →
      ‖H g s‖ ≤ K * ((1 + |s.im|) ^ 2)⁻¹ := by
  obtain ⟨CP, hCP⟩ := norm_Psi_le hg
  obtain ⟨D, hD⟩ := norm_digamma_strip_le
  set K : ℝ := (2 + (2 + Real.log Real.pi / 2 + |D| / 2 + 2 + |D| / 2)) * |CP| with hK
  refine ⟨K, fun s h1 h2 h3 => ?_⟩
  set y : ℝ := s.im with hy
  have hy0 : 0 < 1 + |y| := by positivity
  have hPs := hCP s h1 h2
  have hPnn : 0 ≤ ‖Psi g s‖ := norm_nonneg _
  have hPb : ‖Psi g s‖ ≤ |CP| / (1 + |y|) ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    calc ‖Psi g s‖ * (1 + |y|) ^ 3 = (1 + |y|) ^ 3 * ‖Psi g s‖ := by ring
      _ ≤ |CP| := hPs.trans (le_abs_self _)
  have hs0 : 1 / 2 ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    rw [abs_of_nonneg (by linarith)] at this
    linarith
  have e1 : ‖1 / (s - 1)‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
  have e2 : ‖1 / s‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
  have hl : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have e3 : ‖(-(Real.log Real.pi : ℂ) / 2)‖ = Real.log Real.pi / 2 := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]; simp
  have e4 : ‖Complex.digamma (s / 2) / 2‖ ≤ |D| * (1 + |y|) / 2 := by
    have hsre : (s.re : ℝ) ∈ Icc (1 / 2 : ℝ) 2 := ⟨h1, h2⟩
    have h := hD s.re s.im hsre
    rw [Complex.re_add_im] at h
    rw [norm_div]
    have : D * (1 + |s.im|) ≤ |D| * (1 + |s.im|) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    simp only [Complex.norm_ofNat] 
    linarith
  have hR0 : ‖R0 s‖ ≤ 2 + Real.log Real.pi / 2 + |D| * (1 + |y|) / 2 := by
    unfold R0
    calc _ ≤ ‖1 / s‖ + ‖(-(Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2)‖ := norm_add_le _ _
      _ ≤ ‖1 / s‖ + (‖(-(Real.log Real.pi : ℂ) / 2)‖ + ‖Complex.digamma (s / 2) / 2‖) :=
          add_le_add le_rfl (norm_add_le _ _)
      _ ≤ _ := by linarith
  have hcomb : ‖1 / (s - 1)‖ + ‖R0 s‖ ≤ (2 + (2 + Real.log Real.pi / 2 + |D| / 2 + 2 + |D| / 2)) * (1 + |y|) := by
    have hy1 : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
    have hDn : 0 ≤ |D| := abs_nonneg D
    nlinarith [mul_nonneg hDn (abs_nonneg y), mul_nonneg hl (abs_nonneg y)]
  unfold H
  calc ‖Psi g s / (s - 1) + R0 s * Psi g s‖ ≤ ‖Psi g s / (s - 1)‖ + ‖R0 s * Psi g s‖ := norm_add_le _ _
    _ = (‖1 / (s - 1)‖ + ‖R0 s‖) * ‖Psi g s‖ := by
        simp only [norm_div, norm_mul, norm_one]; ring
    _ ≤ ((2 + (2 + Real.log Real.pi / 2 + |D| / 2 + 2 + |D| / 2)) * (1 + |y|)) * (|CP| / (1 + |y|) ^ 3) :=
        mul_le_mul hcomb hPb hPnn (by positivity)
    _ = K * ((1 + |y|) ^ 2)⁻¹ := by rw [hK]; field_simp


/-- Rectangle `[1/2, 2] × [-T, T]`: the boundary integral of `H` is `2πi Ψ(1)`. -/
theorem rectInt_H {g : ℝ → ℝ} (hg : IsTestFunction g) {T : ℝ} (hT : 1 ≤ T) :
    Complex.rectInt (H g) ((1 / 2 : ℂ) - (T : ℂ) * Complex.I) ((2 : ℂ) + (T : ℂ) * Complex.I) =
      2 * Real.pi * Complex.I * Psi g 1 := by
  have hz : ((1 / 2 : ℂ) - (T : ℂ) * Complex.I).re = 1 / 2 := by simp
  have hw : ((2 : ℂ) + (T : ℂ) * Complex.I).re = 2 := by simp
  have hzi : ((1 / 2 : ℂ) - (T : ℂ) * Complex.I).im = -T := by simp
  have hwi : ((2 : ℂ) + (T : ℂ) * Complex.I).im = T := by simp
  have hbd : ∀ s, Complex.OnRectBoundary ((1 / 2 : ℂ) - (T : ℂ) * Complex.I)
      ((2 : ℂ) + (T : ℂ) * Complex.I) s → 1 / 2 ≤ s.re ∧ s.re ≤ 2 ∧ s ≠ 1 := by
    intro s hs
    rcases hs with ⟨hi, hr⟩ | ⟨hr, hi⟩
    · rw [hz, hw, uIcc_of_le (by norm_num)] at hr
      refine ⟨hr.1, hr.2, fun h => ?_⟩
      rcases hi with hi | hi
      · rw [hzi, h] at hi; simp at hi; linarith
      · rw [hwi, h] at hi; simp at hi; linarith
    · rw [hz, hw] at hr
      refine ⟨by rcases hr with h | h <;> norm_num [h],
        by rcases hr with h | h <;> norm_num [h], fun h => ?_⟩
      rcases hr with hr | hr <;> (rw [h] at hr; norm_num at hr)
  have hA : Complex.EdgeInt (fun s => Psi g s / (s - 1)) ((1 / 2 : ℂ) - (T : ℂ) * Complex.I)
      ((2 : ℂ) + (T : ℂ) * Complex.I) := by
    refine Complex.edgeInt_of_continuousAt_boundary fun s hs => ?_
    obtain ⟨-, -, hs1⟩ := hbd s hs
    exact ((differentiable_Psi hg).continuous.continuousAt).div
      (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 hs1)
  have hB : Complex.EdgeInt (fun s => R0 s * Psi g s) ((1 / 2 : ℂ) - (T : ℂ) * Complex.I)
      ((2 : ℂ) + (T : ℂ) * Complex.I) := by
    refine Complex.edgeInt_of_continuousAt_boundary fun s hs => ?_
    obtain ⟨h1, -, -⟩ := hbd s hs
    exact (continuousAt_R0 (by linarith)).mul (differentiable_Psi hg).continuous.continuousAt
  have h1 : Complex.rectInt (fun s => Psi g s / (s - 1)) ((1 / 2 : ℂ) - (T : ℂ) * Complex.I)
      ((2 : ℂ) + (T : ℂ) * Complex.I) = 2 * Real.pi * Complex.I * Psi g 1 :=
    Complex.rectInt_div_sub (differentiable_Psi hg) (by simp; norm_num)
      (by simp) (by simp; linarith) (by simp; linarith)
  have h2 : Complex.rectInt (fun s => R0 s * Psi g s) ((1 / 2 : ℂ) - (T : ℂ) * Complex.I)
      ((2 : ℂ) + (T : ℂ) * Complex.I) = 0 := by
    refine Complex.rectInt_eq_zero_of_differentiableOn _ _ fun s hs => ?_
    rw [Complex.mem_reProdIm] at hs
    rw [hz, hw, uIcc_of_le (by norm_num)] at hs
    exact ((differentiableAt_R0 (by linarith [hs.1.1])).mul
      ((differentiable_Psi hg) s)).differentiableWithinAt
  unfold H
  rw [Complex.rectInt_add hA hB, h1, h2, add_zero]


theorem continuous_H_line {g : ℝ → ℝ} (hg : IsTestFunction g) {σ : ℝ} (hσ : σ = 1 / 2 ∨ σ = 2) :
    Continuous fun y : ℝ => H g ((σ : ℂ) + y * Complex.I) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hre : 0 < ((σ : ℂ) + y * Complex.I).re := by rcases hσ with rfl | rfl <;> norm_num
  have hne : ((σ : ℂ) + y * Complex.I) - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rcases hσ with rfl | rfl <;> norm_num at this
  have hlin : Continuous fun y : ℝ => (σ : ℂ) + y * Complex.I := by fun_prop
  have hP := (differentiable_Psi hg).continuous
  have hat : ContinuousAt (H g) ((σ : ℂ) + y * Complex.I) := by
    unfold H
    exact (hP.continuousAt.div (continuousAt_id.sub continuousAt_const) hne).add
      ((continuousAt_R0 hre).mul hP.continuousAt)
  exact hat.comp (f := fun y : ℝ => (σ : ℂ) + y * Complex.I) hlin.continuousAt

theorem integrable_H_line {g : ℝ → ℝ} (hg : IsTestFunction g) {σ : ℝ} (hσ : σ = 1 / 2 ∨ σ = 2) :
    Integrable fun y : ℝ => H g ((σ : ℂ) + y * Complex.I) := by
  obtain ⟨K, hK⟩ := norm_H_le hg
  have hint : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (E := ℝ) (μ := volume) (by simp)
  refine (hint.const_mul K).mono' (continuous_H_line hg hσ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hre1 : (1 / 2 : ℝ) ≤ ((σ : ℂ) + y * Complex.I).re := by rcases hσ with rfl | rfl <;> norm_num
  have hre2 : ((σ : ℂ) + y * Complex.I).re ≤ 2 := by rcases hσ with rfl | rfl <;> norm_num
  have hn : 1 / 2 ≤ ‖((σ : ℂ) + y * Complex.I) - 1‖ := by
    have h := Complex.abs_re_le_norm (((σ : ℂ) + y * Complex.I) - 1)
    have e : (((σ : ℂ) + y * Complex.I) - 1).re = σ - 1 := by simp
    rw [e] at h
    refine le_trans ?_ h
    rcases hσ with rfl | rfl <;> norm_num [abs_of_neg, abs_of_pos]
  have := hK _ hre1 hre2 hn
  have e : ((σ : ℂ) + y * Complex.I).im = y := by simp
  rw [e] at this
  have hy0 : 0 < 1 + |y| := by positivity
  have hrp : (1 + ‖y‖) ^ (-(2 : ℝ)) = ((1 + |y|) ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, Real.rpow_neg hy0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  rwa [hrp]

/-- The rectangle integral over `[1/2, 2] × [-T, T]` in line coordinates. -/
theorem rectInt_shift (F : ℂ → ℂ) (T : ℝ) :
    Complex.rectInt F ((1 / 2 : ℂ) - (T : ℂ) * Complex.I) ((2 : ℂ) + (T : ℂ) * Complex.I) =
      (∫ x : ℝ in (1 / 2 : ℝ)..2, F ((x : ℂ) - (T : ℂ) * Complex.I)) -
        (∫ x : ℝ in (1 / 2 : ℝ)..2, F ((x : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I * (∫ y : ℝ in (-T)..T, F (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y : ℝ in (-T)..T, F (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) := by
  unfold Complex.rectInt
  have e1 : ((1 / 2 : ℂ) - (T : ℂ) * Complex.I).re = 1 / 2 := by simp
  have e2 : ((2 : ℂ) + (T : ℂ) * Complex.I).re = 2 := by simp
  have e3 : ((1 / 2 : ℂ) - (T : ℂ) * Complex.I).im = -T := by simp
  have e4 : ((2 : ℂ) + (T : ℂ) * Complex.I).im = T := by simp
  rw [e1, e2, e3, e4]
  simp only [smul_eq_mul, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_div]

/-- **The contour shift.** -/
theorem shift_identity {g : ℝ → ℝ} (hg : IsTestFunction g) :
    (∫ y : ℝ, H g (((2 : ℝ) : ℂ) + y * Complex.I)) -
        ∫ y : ℝ, H g (((1 / 2 : ℝ) : ℂ) + y * Complex.I) = 2 * Real.pi * Psi g 1 := by
  obtain ⟨K, hK⟩ := norm_H_le hg
  have hVR := intervalIntegral_tendsto_integral (integrable_H_line hg (σ := 2) (Or.inr rfl))
    (tendsto_neg_atTop_atBot (G := ℝ)) tendsto_id
  have hVL := intervalIntegral_tendsto_integral (integrable_H_line hg (σ := 1 / 2) (Or.inl rfl))
    (tendsto_neg_atTop_atBot (G := ℝ)) tendsto_id
  -- the horizontal edges vanish
  have hbd : ∀ (e T : ℝ), 1 ≤ T → (e = T ∨ e = -T) → ∀ x ∈ Ι (1 / 2 : ℝ) 2,
      ‖H g ((x : ℂ) + (e : ℂ) * Complex.I)‖ ≤ K * ((1 + T) ^ 2)⁻¹ := by
    intro e T hT he x hx
    rw [uIoc_of_le (by norm_num)] at hx
    have hre1 : (1 / 2 : ℝ) ≤ ((x : ℂ) + (e : ℂ) * Complex.I).re := by simpa using hx.1.le
    have hre2 : ((x : ℂ) + (e : ℂ) * Complex.I).re ≤ 2 := by simpa using hx.2
    have hT0 : 0 ≤ T := by linarith
    have habse : |e| = T := by
      rcases he with he | he
      · rw [he]; exact abs_of_nonneg hT0
      · rw [he, abs_neg]; exact abs_of_nonneg hT0
    have him : |((x : ℂ) + (e : ℂ) * Complex.I).im| = T := by
      simpa using habse
    have hn : 1 / 2 ≤ ‖((x : ℂ) + (e : ℂ) * Complex.I) - 1‖ := by
      have h := Complex.abs_im_le_norm (((x : ℂ) + (e : ℂ) * Complex.I) - 1)
      have e' : (((x : ℂ) + (e : ℂ) * Complex.I) - 1).im = e := by simp
      rw [e'] at h
      linarith
    have := hK _ hre1 hre2 hn
    rw [him] at this
    exact this
  have hh : Tendsto (fun T : ℝ => K * ((1 + T) ^ 2)⁻¹ * (3 / 2)) atTop (nhds 0) := by
    have : Tendsto (fun T : ℝ => (1 + T) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
        (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    simpa using ((this.inv_tendsto_atTop).const_mul K).mul_const (3 / 2 : ℝ)
  have hhor : Tendsto (fun T : ℝ =>
      (∫ x : ℝ in (1 / 2 : ℝ)..2, H g ((x : ℂ) - (T : ℂ) * Complex.I)) -
        (∫ x : ℝ in (1 / 2 : ℝ)..2, H g ((x : ℂ) + (T : ℂ) * Complex.I))) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using hh.const_mul 2)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have b1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 : ℝ)) (b := 2)
      (f := fun x : ℝ => H g ((x : ℂ) - (T : ℂ) * Complex.I))
      (C := K * ((1 + T) ^ 2)⁻¹) (fun x hx => by
        have := hbd (-T) T hT (Or.inr rfl) x hx
        simpa [sub_eq_add_neg] using this)
    have b2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 : ℝ)) (b := 2)
      (f := fun x : ℝ => H g ((x : ℂ) + (T : ℂ) * Complex.I))
      (C := K * ((1 + T) ^ 2)⁻¹) (fun x hx => hbd T T hT (Or.inl rfl) x hx)
    have habs : |(2 : ℝ) - 1 / 2| = 3 / 2 := by norm_num
    rw [habs] at b1 b2
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hT : Tendsto (fun T : ℝ =>
      ((∫ x : ℝ in (1 / 2 : ℝ)..2, H g ((x : ℂ) - (T : ℂ) * Complex.I)) -
        (∫ x : ℝ in (1 / 2 : ℝ)..2, H g ((x : ℂ) + (T : ℂ) * Complex.I))) +
        Complex.I * ((∫ y : ℝ in (-T)..T, H g (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) -
          ∫ y : ℝ in (-T)..T, H g (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I))) atTop
      (nhds (0 + Complex.I * ((∫ y : ℝ, H g (((2 : ℝ) : ℂ) + y * Complex.I)) -
        ∫ y : ℝ, H g (((1 / 2 : ℝ) : ℂ) + y * Complex.I)))) :=
    hhor.add ((hVR.sub hVL).const_mul Complex.I)
  have hconst : Tendsto (fun T : ℝ =>
      ((∫ x : ℝ in (1 / 2 : ℝ)..2, H g ((x : ℂ) - (T : ℂ) * Complex.I)) -
        (∫ x : ℝ in (1 / 2 : ℝ)..2, H g ((x : ℂ) + (T : ℂ) * Complex.I))) +
        Complex.I * ((∫ y : ℝ in (-T)..T, H g (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) -
          ∫ y : ℝ in (-T)..T, H g (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I))) atTop
      (nhds (2 * Real.pi * Complex.I * Psi g 1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    rw [← rectInt_H hg hT, rectInt_shift]
    ring
  have := tendsto_nhds_unique hconst hT
  rw [zero_add] at this
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  apply mul_left_cancel₀ hI
  rw [← this]
  ring

end GppShiftContour
