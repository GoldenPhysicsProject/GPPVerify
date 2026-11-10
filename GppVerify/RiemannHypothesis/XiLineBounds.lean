/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.Real.Pi.Bounds
import GppVerify.RiemannHypothesis.PrimeLine
import GppVerify.RiemannHypothesis.XiReflection
import GppVerify.RiemannHypothesis.DigammaVerticalBound
import GppVerify.RiemannHypothesis.ExplicitFormulaE1Wide

/-!
# Explicit formula, stage E6d (bounds): `ξ'/ξ` on the line `Re s = 2`

`‖ξ'/ξ (2 + i y)‖ ≤ C (1 + |y|)`. Together with the decay of the spectral transform this makes every
integral over the line `Re s = 2` in the contour argument absolutely convergent.
-/

open Complex Set MeasureTheory GppMeyerSpectralWeil GppExplicitFormulaE1 GppSpectralInversion
open scoped ArithmeticFunction.vonMangoldt

namespace GppXiLineBounds

open GppLogDerivZeroFree GppXiZeroCounting

/-- `ζ'/ζ` is bounded on `Re s = 2`, by the Dirichlet series of `Λ`. -/
theorem norm_zeta_logDeriv_line_le :
    ∃ C : ℝ, ∀ y : ℝ, ‖deriv riemannZeta ((2 : ℝ) + y * Complex.I : ℂ) /
      riemannZeta ((2 : ℝ) + y * Complex.I : ℂ)‖ ≤ C := by
  set f : ℕ → ℂ := fun m => (ArithmeticFunction.vonMangoldt m : ℂ) with hf
  have hsumm : Summable (fun n => ‖LSeries.term f ((2 : ℝ) : ℂ) n‖) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((2 : ℝ) : ℂ)) (by simp)).norm
  refine ⟨∑' n, ‖LSeries.term f ((2 : ℝ) : ℂ) n‖, fun y => ?_⟩
  have hre : 1 < (((2 : ℝ) + y * Complex.I : ℂ)).re := by simp
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  have hnorm : ∀ n, ‖LSeries.term f ((2 : ℝ) + y * Complex.I : ℂ) n‖ =
      ‖LSeries.term f ((2 : ℝ) : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  have hs : Summable (fun n => ‖LSeries.term f ((2 : ℝ) + y * Complex.I : ℂ) n‖) := by
    exact hsumm.congr (fun n => (hnorm n).symm)
  have : ‖deriv riemannZeta ((2 : ℝ) + y * Complex.I : ℂ) /
      riemannZeta ((2 : ℝ) + y * Complex.I : ℂ)‖ =
      ‖∑' n, LSeries.term f ((2 : ℝ) + y * Complex.I : ℂ) n‖ := by
    rw [← norm_neg, ← neg_div, ← hL]
    rfl
  rw [this]
  refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq ?_)
  exact tsum_congr hnorm

/-- `ψ` is continuous on the open right half-plane. -/
theorem continuousAt_digamma {z : ℂ} (hz : 0 < z.re) : ContinuousAt Complex.digamma z := by
  have hne : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : AnalyticAt ℂ Complex.Gamma z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hopen.mem_nhds hz] with w hw
    refine Complex.differentiableAt_Gamma w (fun m h => ?_)
    have := congrArg Complex.re h
    simp at this
    have hw' : 0 < w.re := hw
    linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have h : Complex.digamma = fun w => deriv Complex.Gamma w / Complex.Gamma w := by
    funext w; rw [Complex.digamma_def, logDeriv_apply]
  rw [h]
  exact (hG.deriv.div hG (Complex.Gamma_ne_zero hne)).continuousAt

/-- `ψ((2 + i y)/2)` grows at most linearly in `y`. -/
theorem norm_digamma_half_line_le :
    ∃ C : ℝ, ∀ y : ℝ, ‖Complex.digamma ((((2 : ℝ) : ℂ) + y * Complex.I) / 2)‖ ≤ C * (1 + |y|) := by
  obtain ⟨C1, hC1⟩ := GppDigammaVertical.norm_digamma_le 1 (by norm_num)
  -- continuity on the compact piece
  have hcont : Continuous fun y : ℝ => Complex.digamma ((((2 : ℝ) : ℂ) + y * Complex.I) / 2) := by
    have hlin : Continuous fun y : ℝ => (((2 : ℝ) : ℂ) + y * Complex.I) / 2 := by fun_prop
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hy : 0 < ((((2 : ℝ) : ℂ) + y * Complex.I) / 2).re := by simp
    exact (continuousAt_digamma hy).comp (f := fun y : ℝ => (((2 : ℝ) : ℂ) + y * Complex.I) / 2)
      hlin.continuousAt
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨|B| + |C1|, fun y => ?_⟩
  rcases le_or_gt 2 |y| with hy | hy
  · have him : 1 ≤ |((((2 : ℝ) : ℂ) + y * Complex.I) / 2).im| := by
      simp
      rw [abs_div, abs_two]
      linarith
    have hre : |((((2 : ℝ) : ℂ) + y * Complex.I) / 2).re| ≤ 1 := by simp
    have h := hC1 _ hre him
    have himabs : |((((2 : ℝ) : ℂ) + y * Complex.I) / 2).im| = |y| / 2 := by
      simp [abs_div]
    rw [himabs] at h
    have hlog : Real.log (|y| / 2 + 1) ≤ |y| / 2 := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < |y| / 2 + 1)
      linarith
    have hC : 0 ≤ |C1| := abs_nonneg _
    have : C1 * Real.log (|y| / 2 + 1) ≤ |C1| * (|y| / 2) := by
      calc C1 * Real.log (|y| / 2 + 1) ≤ |C1| * Real.log (|y| / 2 + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.log_nonneg (by linarith [abs_nonneg y]))
        _ ≤ |C1| * (|y| / 2) := mul_le_mul_of_nonneg_left hlog hC
    have hB0 : 0 ≤ |B| := abs_nonneg _
    nlinarith [abs_nonneg y]
  · have hyI : y ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [abs_lt.1 hy], by linarith [abs_lt.1 hy]⟩
    have := hB y hyI
    have hB0 : 0 ≤ |B| := abs_nonneg _
    have hC0 : 0 ≤ |C1| := abs_nonneg _
    nlinarith [le_abs_self B, abs_nonneg y]


/-- **`ξ'/ξ` grows at most linearly on `Re s = 2`.** -/
theorem norm_logDeriv_xi_line_le :
    ∃ C : ℝ, ∀ y : ℝ, ‖logDeriv xi (((2 : ℝ) : ℂ) + y * Complex.I)‖ ≤ C * (1 + |y|) := by
  obtain ⟨C1, h1⟩ := norm_zeta_logDeriv_line_le
  obtain ⟨C2, h2⟩ := norm_digamma_half_line_le
  refine ⟨1 / 2 + 1 + Real.log Real.pi / 2 + |C2| / 2 + |C1| + 1, fun y => ?_⟩
  have hre : (((2 : ℝ) : ℂ) + y * Complex.I).re = 2 := by simp
  have hs1 : (((2 : ℝ) : ℂ) + y * Complex.I) ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this
  have hxi := GppXiReflection.xi_ne_zero_of_one_le_re (s := ((2 : ℝ) : ℂ) + y * Complex.I) (by rw [hre]; norm_num)
  rw [logDeriv_xi_eq (by rw [hre]; norm_num) hs1 hxi]
  set s : ℂ := ((2 : ℝ) : ℂ) + y * Complex.I with hs
  have hn : 2 ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    rw [hre] at this; simpa using this
  have hn1 : 1 ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    have h2 : (s - 1).re = 1 := by simp [hre]; norm_num
    rw [h2] at this; norm_num at this; exact this
  have a1 : ‖1 / s‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]; exact one_div_le_one_div_of_le (by norm_num) hn
  have a2 : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]; exact (div_le_one (by linarith)).2 hn1
  have a3 : ‖(-(Real.log Real.pi : ℂ) / 2)‖ ≤ Real.log Real.pi / 2 := by
    have hl : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]; simp
  have a4 : ‖Complex.digamma (s / 2) / 2‖ ≤ |C2| * (1 + |y|) / 2 := by
    rw [norm_div]
    have := h2 y
    have h0 : C2 * (1 + |y|) ≤ |C2| * (1 + |y|) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    simp; linarith
  have a5 := h1 y
  have hy := abs_nonneg y
  have hz : ‖deriv riemannZeta s / riemannZeta s‖ ≤ |C1| := a5.trans (le_abs_self _)
  have hlog : logDeriv riemannZeta s = deriv riemannZeta s / riemannZeta s := rfl
  rw [hlog]
  have t1 := norm_add_le (1 / s + 1 / (s - 1) + (-(Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2))
    (deriv riemannZeta s / riemannZeta s)
  have t2 := norm_add_le (1 / s + 1 / (s - 1)) (-(Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2)
  have t3 := norm_add_le (1 / s) (1 / (s - 1))
  have t4 := norm_add_le (-(Real.log Real.pi : ℂ) / 2) (Complex.digamma (s / 2) / 2)
  calc _ ≤ ‖1 / s‖ + ‖1 / (s - 1)‖ + (‖(-(Real.log Real.pi : ℂ) / 2)‖ +
        ‖Complex.digamma (s / 2) / 2‖) + ‖deriv riemannZeta s / riemannZeta s‖ := by linarith
    _ ≤ _ := by
      have hl : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
      have hc : 0 ≤ |C2| := abs_nonneg _
      have hc1 : 0 ≤ |C1| := abs_nonneg _
      nlinarith [mul_nonneg hl hy, mul_nonneg hc hy, mul_nonneg hc1 hy]

end GppXiLineBounds
