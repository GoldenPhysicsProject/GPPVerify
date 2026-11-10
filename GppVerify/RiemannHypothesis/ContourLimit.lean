/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.XiLineBounds
import GppVerify.RiemannHypothesis.XiZeroCounting
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


/-- **The zero sum converges absolutely.** -/
theorem summable_zeroSum {g : ℝ → ℝ} (hg : IsTestFunction g) :
    Summable (fun ρ : nontrivialZeros => (zeroMult ρ : ℂ) * spectralTransform g ρ) := by
  obtain ⟨N, hN⟩ := zeroCountingPolynomial
  obtain ⟨C0, hC0⟩ := GppExplicitFormulaE1.spectralTransform_decay_wide hg (1 / 2) 0
  obtain ⟨CN, hCN⟩ := GppExplicitFormulaE1.spectralTransform_decay_wide hg (1 / 2) N
  set C' : ℝ := 2 ^ N * ((3 / 2) ^ N * |C0| + |CN|) with hC'
  refine Summable.of_norm_bounded (hN.mul_left C') fun ρ => ?_
  have hre : |(ρ : ℂ).re - 1 / 2| ≤ 1 / 2 := by
    obtain ⟨-, h0, h1⟩ := ρ.2
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h0 := hC0 ρ hre
  have hN' := hCN ρ hre
  simp only [pow_zero, one_mul] at h0
  set x : ℝ := ‖(ρ : ℂ) - 1 / 2‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have hΦ0 : 0 ≤ ‖spectralTransform g ρ‖ := norm_nonneg _
  have hle : 1 + ‖(ρ : ℂ)‖ ≤ 3 / 2 + x := by
    have : ‖(ρ : ℂ)‖ ≤ ‖(ρ : ℂ) - 1 / 2‖ + ‖(1 / 2 : ℂ)‖ := by
      calc ‖(ρ : ℂ)‖ = ‖((ρ : ℂ) - 1 / 2) + 1 / 2‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    linarith
  have hpow : (1 + ‖(ρ : ℂ)‖) ^ N ≤ 2 ^ N * ((3 / 2) ^ N + x ^ N) := by
    calc (1 + ‖(ρ : ℂ)‖) ^ N ≤ (3 / 2 + x) ^ N :=
          pow_le_pow_left₀ (by positivity) hle N
      _ ≤ (2 * max (3 / 2) x) ^ N := by
          apply pow_le_pow_left₀ (by positivity)
          have := le_max_left (3 / 2 : ℝ) x
          have := le_max_right (3 / 2 : ℝ) x
          linarith
      _ = 2 ^ N * max (3 / 2) x ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * ((3 / 2) ^ N + x ^ N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rcases le_total (3 / 2 : ℝ) x with h | h
          · rw [max_eq_right h]; have : 0 ≤ (3 / 2 : ℝ) ^ N := by positivity
            linarith
          · rw [max_eq_left h]; have : 0 ≤ x ^ N := by positivity
            linarith
  have hprod : (1 + ‖(ρ : ℂ)‖) ^ N * ‖spectralTransform g ρ‖ ≤ C' := by
    calc (1 + ‖(ρ : ℂ)‖) ^ N * ‖spectralTransform g ρ‖
        ≤ 2 ^ N * ((3 / 2) ^ N + x ^ N) * ‖spectralTransform g ρ‖ :=
          mul_le_mul_of_nonneg_right hpow hΦ0
      _ = 2 ^ N * ((3 / 2) ^ N * ‖spectralTransform g ρ‖ + x ^ N * ‖spectralTransform g ρ‖) := by ring
      _ ≤ 2 ^ N * ((3 / 2) ^ N * |C0| + |CN|) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have a1 : ‖spectralTransform g ρ‖ ≤ |C0| := h0.trans (le_abs_self _)
          have a2 : x ^ N * ‖spectralTransform g ρ‖ ≤ |CN| := hN'.trans (le_abs_self _)
          have := mul_le_mul_of_nonneg_left a1 (by positivity : (0 : ℝ) ≤ (3 / 2) ^ N)
          linarith
  have hm : (0 : ℝ) ≤ zeroMult ρ := Nat.cast_nonneg _
  have hpos : (0 : ℝ) < (1 + ‖(ρ : ℂ)‖) ^ N := by positivity
  rw [norm_mul, Complex.norm_natCast]
  calc (zeroMult ρ : ℝ) * ‖spectralTransform g ρ‖
      = (zeroMult ρ : ℝ) * (((1 + ‖(ρ : ℂ)‖) ^ N)⁻¹ * ((1 + ‖(ρ : ℂ)‖) ^ N * ‖spectralTransform g ρ‖)) := by
        field_simp
    _ ≤ (zeroMult ρ : ℝ) * (((1 + ‖(ρ : ℂ)‖) ^ N)⁻¹ * C') :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod (by positivity)) hm
    _ = C' * ((zeroMult ρ : ℝ) * ((1 + ‖(ρ : ℂ)‖) ^ N)⁻¹) := by ring


/-- Polynomial decay of `Φ_g` of any order on the wide strip, in the form `(1+‖s-1/2‖)^N ‖Φ‖ ≤ C`. -/
theorem poly_decay {g : ℝ → ℝ} (hg : IsTestFunction g) (M : ℝ) (N : ℕ) :
    ∃ C, ∀ s : ℂ, |s.re - 1 / 2| ≤ M → (1 + ‖s - 1 / 2‖) ^ N * ‖spectralTransform g s‖ ≤ C := by
  obtain ⟨C0, hC0⟩ := GppExplicitFormulaE1.spectralTransform_decay_wide hg M 0
  obtain ⟨CN, hCN⟩ := GppExplicitFormulaE1.spectralTransform_decay_wide hg M N
  refine ⟨2 ^ N * (|C0| + |CN|), fun s hs => ?_⟩
  have h0 := hC0 s hs
  have hN := hCN s hs
  simp only [pow_zero, one_mul] at h0
  set x : ℝ := ‖s - 1 / 2‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have hΦ0 : 0 ≤ ‖spectralTransform g s‖ := norm_nonneg _
  have hpow : (1 + x) ^ N ≤ 2 ^ N * (1 + x ^ N) := by
    calc (1 + x) ^ N ≤ (2 * max 1 x) ^ N := by
          apply pow_le_pow_left₀ (by positivity)
          have := le_max_left (1 : ℝ) x
          have := le_max_right (1 : ℝ) x
          linarith
      _ = 2 ^ N * max 1 x ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + x ^ N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rcases le_total (1 : ℝ) x with h | h
          · rw [max_eq_right h]; have : (0 : ℝ) ≤ 1 := by norm_num
            linarith
          · rw [max_eq_left h, one_pow]; have : 0 ≤ x ^ N := by positivity
            linarith
  calc (1 + x) ^ N * ‖spectralTransform g s‖ ≤ 2 ^ N * (1 + x ^ N) * ‖spectralTransform g s‖ :=
        mul_le_mul_of_nonneg_right hpow hΦ0
    _ = 2 ^ N * (‖spectralTransform g s‖ + x ^ N * ‖spectralTransform g s‖) := by ring
    _ ≤ 2 ^ N * (|C0| + |CN|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [le_abs_self C0, le_abs_self CN]

/-- **Horizontal sides.** At suitable heights the two horizontal edges contribute `O(1/t)`. -/
theorem exists_horizontal {g : ℝ → ℝ} (hg : IsTestFunction g) :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T → ∃ t ∈ Icc T (T + 1),
      (∀ σ ∈ Icc (-1 : ℝ) 2, xi ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) ∧
      ‖(∫ x : ℝ in (-1 : ℝ)..2, logDeriv xi ((x : ℂ) - (t : ℂ) * Complex.I) *
            spectralTransform g ((x : ℂ) - (t : ℂ) * Complex.I)) -
        (∫ x : ℝ in (-1 : ℝ)..2, logDeriv xi ((x : ℂ) + (t : ℂ) * Complex.I) *
            spectralTransform g ((x : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C / t := by
  obtain ⟨K, C1, hC1, hgood⟩ := exists_good_height
  obtain ⟨Cd, hCd⟩ := poly_decay hg (3 / 2) (K + 1)
  refine ⟨6 * C1 * |Cd|, fun T hT => ?_⟩
  obtain ⟨t, htI, ht⟩ := hgood T hT
  have ht1 : 1 ≤ t := hT.trans htI.1
  have htpos : 0 < t := by linarith
  refine ⟨t, htI, fun σ hσ => (ht σ hσ).1, ?_⟩
  -- pointwise bound on both edges
  have key : ∀ s : ℂ, |s.im| = t → |s.re - 1 / 2| ≤ 3 / 2 →
      ‖logDeriv xi s‖ ≤ C1 * t ^ K → ‖logDeriv xi s * spectralTransform g s‖ ≤ C1 * |Cd| / t := by
    intro s him hre hld
    have hs := hCd s hre
    have hn : t ≤ ‖s - 1 / 2‖ := by
      have h := Complex.abs_im_le_norm (s - 1 / 2)
      have e : (s - 1 / 2).im = s.im := by simp
      rw [e] at h
      rw [← him]; exact h
    have hpowle : t ^ (K + 1) ≤ (1 + ‖s - 1 / 2‖) ^ (K + 1) :=
      pow_le_pow_left₀ htpos.le (by linarith) _
    have hΦ : ‖spectralTransform g s‖ ≤ |Cd| / t ^ (K + 1) := by
      rw [le_div_iff₀ (by positivity)]
      calc ‖spectralTransform g s‖ * t ^ (K + 1) ≤
            ‖spectralTransform g s‖ * (1 + ‖s - 1 / 2‖) ^ (K + 1) :=
            mul_le_mul_of_nonneg_left hpowle (norm_nonneg _)
        _ = (1 + ‖s - 1 / 2‖) ^ (K + 1) * ‖spectralTransform g s‖ := by ring
        _ ≤ |Cd| := hs.trans (le_abs_self _)
    rw [norm_mul]
    calc ‖logDeriv xi s‖ * ‖spectralTransform g s‖ ≤ (C1 * t ^ K) * (|Cd| / t ^ (K + 1)) :=
          mul_le_mul hld hΦ (norm_nonneg _) (by positivity)
      _ = C1 * |Cd| / t := by field_simp; ring
  have hbound : ∀ (e : ℝ), (e = t ∨ e = -t) → ∀ x ∈ Ι (-1 : ℝ) 2,
      ‖logDeriv xi ((x : ℂ) + (e : ℂ) * Complex.I) *
        spectralTransform g ((x : ℂ) + (e : ℂ) * Complex.I)‖ ≤ C1 * |Cd| / t := by
    intro e he x hx
    rw [uIoc_of_le (by norm_num)] at hx
    have hxI : x ∈ Icc (-1 : ℝ) 2 := ⟨hx.1.le, hx.2⟩
    have him : |((x : ℂ) + (e : ℂ) * Complex.I).im| = t := by
      simp; rcases he with he | he <;> rw [he] <;> simp [abs_of_pos htpos]
    have hre : |((x : ℂ) + (e : ℂ) * Complex.I).re - 1 / 2| ≤ 3 / 2 := by
      simp; exact abs_le.2 ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
    refine key _ him hre ?_
    rcases he with he | he
    · rw [he]; exact (ht x hxI).2
    · rw [he]
      have h1 : ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) =
          1 - (((1 - x : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
        apply Complex.ext <;> simp
      rw [h1, logDeriv_xi_one_sub, norm_neg]
      exact (ht (1 - x) ⟨by linarith [hxI.2], by linarith [hxI.1]⟩).2
  have b1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 2)
    (f := fun x : ℝ => logDeriv xi ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) *
        spectralTransform g ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)) (hbound (-t) (Or.inr rfl))
  have b2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 2)
    (f := fun x : ℝ => logDeriv xi ((x : ℂ) + (t : ℂ) * Complex.I) *
        spectralTransform g ((x : ℂ) + (t : ℂ) * Complex.I)) (hbound t (Or.inl rfl))
  have e1 : (fun x : ℝ => logDeriv xi ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) *
        spectralTransform g ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)) =
      fun x : ℝ => logDeriv xi ((x : ℂ) - (t : ℂ) * Complex.I) *
        spectralTransform g ((x : ℂ) - (t : ℂ) * Complex.I) := by
    funext x; push_cast; ring_nf
  rw [e1] at b1
  have habs : |(2 : ℝ) - (-1)| = 3 := by norm_num
  rw [habs] at b1 b2
  refine (norm_sub_le _ _).trans ?_
  calc _ ≤ C1 * |Cd| / t * 3 + C1 * |Cd| / t * 3 := add_le_add b1 b2
    _ = 6 * C1 * |Cd| / t := by ring

end GppContourLimit
