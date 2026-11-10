/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.XiLineBounds
import GppVerify.RiemannHypothesis.XiLogDerivative
import GppVerify.Upstream.RectangleLogDerivative

/-!
# Explicit formula, stage E6d: the contour identity

* `differentiable_spectralTransform`: `Φ_g` is entire for a test function `g`.
-/

open Complex Set MeasureTheory Metric Filter Topology GppMeyerSpectralWeil
open scoped Interval

namespace GppContourLimit

/-- The spectral transform of a test function is entire. -/
theorem differentiable_spectralTransform {g : ℝ → ℝ} (hg : IsTestFunction g) :
    Differentiable ℂ (spectralTransform g) := by
  intro s0
  obtain ⟨M, hM⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨A0, hA0⟩ := hg.2.isCompact.isBounded.subset_closedBall (0 : ℝ)
  set A : ℝ := |A0| with hAdef
  have hA : tsupport g ⊆ closedBall 0 A := hA0.trans (closedBall_subset_closedBall (le_abs_self _))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hAnn : 0 ≤ A := abs_nonneg _
  have hsupp : ∀ u, g u ≠ 0 → |u| ≤ A := by
    intro u hu
    have := hA (subset_tsupport _ (Function.mem_support.2 hu))
    simpa using this
  set B : ℝ := M * A * Real.exp ((|s0.re| + 1 + 1 / 2) * A) with hB
  have hgc : Continuous g := hg.1.continuous
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
    (F := fun (s : ℂ) (u : ℝ) => (g u : ℂ) * Complex.exp ((s - 1 / 2) * u))
    (F' := fun (s : ℂ) (u : ℝ) => (g u : ℂ) * (u * Complex.exp ((s - 1 / 2) * u)))
    (x₀ := s0) (s := ball s0 1) (bound := fun u => B * (Icc (-A) A).indicator 1 u)
    (ball_mem_nhds s0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2.differentiableAt
  · exact Filter.Eventually.of_forall fun s =>
      (by fun_prop : Continuous fun u : ℝ => (g u : ℂ) * Complex.exp ((s - 1 / 2) * u)).aestronglyMeasurable
  · exact (by fun_prop : Continuous fun u : ℝ => (g u : ℂ) * Complex.exp ((s0 - 1 / 2) * u)).integrable_of_hasCompactSupport
      ((hg.2.comp_left Complex.ofReal_zero).mul_right)
  · exact (by fun_prop : Continuous fun u : ℝ => (g u : ℂ) * (u * Complex.exp ((s0 - 1 / 2) * u))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u s hs => ?_
    by_cases hu : g u = 0
    · simp only [hu, Complex.ofReal_zero, zero_mul, norm_zero]
      exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    · have hu' := hsupp u hu
      have hmem : u ∈ Icc (-A) A := ⟨by linarith [(abs_le.1 hu').1], (abs_le.1 hu').2⟩
      rw [Set.indicator_of_mem hmem]
      simp only [Pi.one_apply, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp]
      have hsr : |s.re - s0.re| < 1 := by
        have := Complex.abs_re_le_norm (s - s0)
        rw [mem_ball, dist_eq_norm] at hs
        simp at this
        exact lt_of_le_of_lt this hs
      have hre : ((s - 1 / 2) * (u : ℂ)).re = (s.re - 1 / 2) * u := by simp
      rw [hre]
      have h1 : |g u| ≤ M := (Real.norm_eq_abs _ ▸ hM u)
      have h4 : (s.re - 1 / 2) * u ≤ (|s0.re| + 1 + 1 / 2) * A := by
        calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
          _ = |s.re - 1 / 2| * |u| := abs_mul _ _
          _ ≤ (|s0.re| + 1 + 1 / 2) * A := by
            apply mul_le_mul _ hu' (abs_nonneg _) (by positivity)
            have := abs_sub_abs_le_abs_sub s.re s0.re
            calc |s.re - 1 / 2| ≤ |s.re| + 1 / 2 := by
                  calc |s.re - 1 / 2| ≤ |s.re| + |1 / 2| := abs_sub _ _
                    _ = |s.re| + 1 / 2 := by norm_num
              _ ≤ |s0.re| + 1 + 1 / 2 := by linarith [abs_nonneg (s.re - s0.re), abs_sub_abs_le_abs_sub s.re s0.re]
      have hA0 : 0 ≤ A := (abs_nonneg u).trans hu'
      calc |g u| * (|u| * Real.exp ((s.re - 1 / 2) * u)) ≤ M * (A * Real.exp ((|s0.re| + 1 + 1 / 2) * A)) := by
            apply mul_le_mul h1 _ (by positivity) ((abs_nonneg _).trans h1)
            exact mul_le_mul hu' (Real.exp_le_exp.2 h4) (Real.exp_pos _).le hA0
        _ = B := by rw [hB]; ring
  · have h : Integrable ((Icc (-A) A).indicator (fun _ : ℝ => (1 : ℝ))) :=
      (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
    exact h.const_mul B
  · refine Filter.Eventually.of_forall fun u s _ => ?_
    have h1 : HasDerivAt (fun s : ℂ => (s - 1 / 2) * (u : ℂ)) (u : ℂ) s := by
      simpa using ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).mul_const (u : ℂ)
    have h2 := (h1.cexp).const_mul (g u : ℂ)
    exact h2.congr_deriv (by ring)


open GppLogDerivZeroFree GppXiZeroCounting GppXiReflection GppWeilCriterion

/-- `ξ` does not vanish on the boundary of `Q_t = [-1,2] × [-t,t]` at a good height `t`. -/
theorem xi_ne_zero_boundary {t : ℝ}
    (hgood : ∀ σ ∈ Icc (-1 : ℝ) 2, xi ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    {s : ℂ} (hs : Complex.OnRectBoundary ((-1 : ℂ) - (t : ℂ) * Complex.I)
      ((2 : ℂ) + (t : ℂ) * Complex.I) s) : xi s ≠ 0 := by
  rcases hs with ⟨hi, hr⟩ | ⟨hr, _⟩
  · have hre : s.re ∈ Icc (-1 : ℝ) 2 := by
      rw [uIcc_of_le (by simp; norm_num)] at hr
      simpa using hr
    have hs' : s = (s.re : ℂ) + (s.im : ℂ) * Complex.I := (Complex.re_add_im s).symm
    rcases hi with hi | hi
    · have him : s.im = -t := by simpa using hi
      have h1 : s = 1 - (((1 - s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
        apply Complex.ext <;> simp [him]
      rw [h1, show xi (1 - (((1 - s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
        xi (((1 - s.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) from by
          exact xi_one_sub _]
      exact hgood _ ⟨by linarith [hre.2], by linarith [hre.1]⟩
    · have him : s.im = t := by simpa using hi
      rw [hs']
      rw [him]
      exact hgood _ hre
  · rcases hr with hr | hr
    · exact xi_ne_zero_of_re_le_zero (by simp at hr; linarith)
    · exact xi_ne_zero_of_one_le_re (by simp at hr; linarith)


/-- **The rectangle identity at a good height.** The zeros of `ξ` in `[-1,2] × (-t,t)` are exactly
the nontrivial zeros with `|Im ρ| < t`, and the boundary integral of `(ξ'/ξ) Φ` is `2πi` times the
multiplicity-weighted sum of `Φ` over them. -/
theorem rect_identity {g : ℝ → ℝ} (hg : IsTestFunction g) {t : ℝ} (ht : 1 ≤ t)
    (hgood : ∀ σ ∈ Icc (-1 : ℝ) 2, xi ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    ∃ S : Finset ℂ, (∀ ρ, ρ ∈ S ↔ ρ ∈ nontrivialZeros ∧ |ρ.im| < t) ∧
      Complex.rectInt (fun s => logDeriv xi s * spectralTransform g s)
          ((-1 : ℂ) - (t : ℂ) * Complex.I) ((2 : ℂ) + (t : ℂ) * Complex.I) =
        2 * Real.pi * Complex.I * ∑ ρ ∈ S, (zeroMult ρ : ℂ) * spectralTransform g ρ := by
  obtain ⟨R, hRI, hRz⟩ := exists_radius_no_zero (t + 3)
  have hRpos : 0 < R := by linarith [hRI.1]
  have hsub : [[((-1 : ℂ) - (t : ℂ) * Complex.I).re, ((2 : ℂ) + (t : ℂ) * Complex.I).re]] ×ℂ
      [[((-1 : ℂ) - (t : ℂ) * Complex.I).im, ((2 : ℂ) + (t : ℂ) * Complex.I).im]] ⊆
        ball (0 : ℂ) R := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    obtain ⟨h1, h2⟩ := hz
    simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im,
      Complex.add_im, Complex.mul_im, Complex.neg_im, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, mul_one,
      sub_zero, zero_sub, neg_zero, add_zero, zero_add] at h1 h2
    rw [uIcc_of_le (by norm_num)] at h1
    rw [uIcc_of_le (by linarith)] at h2
    rw [mem_ball, dist_zero_right]
    have hre : |z.re| ≤ 2 := abs_le.2 ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have him : |z.im| ≤ t := abs_le.2 ⟨by linarith [h2.1], by linarith [h2.2]⟩
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ < R := by linarith [hRI.1]
  obtain ⟨S0, hS0, hS1, hS2⟩ := Complex.rectInt_logDeriv_mul differentiable_xi
    (differentiable_spectralTransform hg) xi_zero_ne hRpos hRz
    (z := (-1 : ℂ) - (t : ℂ) * Complex.I) (w := (2 : ℂ) + (t : ℂ) * Complex.I)
    (by simp; constructor <;> linarith) hsub
    (fun s hs => xi_ne_zero_boundary hgood hs)
  refine ⟨S0, fun ρ => ?_, ?_⟩
  · constructor
    · intro hρ
      obtain ⟨h1, h2, h3⟩ := hS0 ρ hρ
      refine ⟨(xi_eq_zero_iff_nontrivial ρ).1 h3, ?_⟩
      simp at h2
      exact abs_lt.2 ⟨by linarith [h2.1], h2.2⟩
    · rintro ⟨hρ, him⟩
      have hx := (xi_eq_zero_iff_nontrivial ρ).2 hρ
      obtain ⟨h0, h1⟩ := xi_zero_mem_strip hx
      refine hS1 ρ ?_ ?_ hx
      · simp; constructor <;> linarith
      · simp; exact ⟨by linarith [(abs_lt.1 him).1], (abs_lt.1 him).2⟩
  · rw [hS2]
    congr 1
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    obtain ⟨h1, h2, h3⟩ := hS0 ρ hρ
    have hρball : ρ ∈ ball (0 : ℂ) R := by
      simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im,
        Complex.add_im, Complex.mul_im, Complex.neg_im, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, mul_one,
        sub_zero, zero_sub, neg_zero, add_zero, zero_add] at h1 h2
      rw [mem_ball, dist_zero_right]
      have hre : |ρ.re| ≤ 2 := abs_le.2 ⟨by linarith [h1.1], by linarith [h1.2]⟩
      have him : |ρ.im| ≤ t := abs_le.2 ⟨by linarith [h2.1], by linarith [h2.2]⟩
      calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
        _ < R := by linarith [hRI.1]
    rw [divisor_xi_apply_set hρball]
    rw [zeroMult_eq_orderNat_xi ((xi_eq_zero_iff_nontrivial ρ).1 h3)]
    simp

end GppContourLimit
