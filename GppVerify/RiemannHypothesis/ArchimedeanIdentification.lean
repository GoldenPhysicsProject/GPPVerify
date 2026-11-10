/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import GppVerify.RiemannHypothesis.DigammaIntegral
import GppVerify.RiemannHypothesis.ExplicitFormulaE1Decay
import GppVerify.RiemannHypothesis.ArithmeticReflectionPositivity

/-!
# Explicit formula, stage E6 (Archimedean term), part 2: the identification

For an even test function `g` with `h(r) = ĝ(1/2 + i r) = ∫ g(u) e^{i r u} du`,

  `archimedeanTerm g = -g(0) log π + (1/2π) ∫ h(r) Re ψ(1/4 + i r/2) dr`.

Proof: Gauss's integral for `ψ` (part 1), Fubini in `(r, t)`, and Fourier inversion
`(1/2π) ∫ h(r) cos(r v) dr = g(v)`.
-/

open Complex Set MeasureTheory FourierTransform SchwartzMap GppMeyerSpectralWeil GppExplicitFormulaE1

namespace GppArchimedeanId

/-- The kernel of Gauss's integral at `z`. -/
noncomputable def K (z : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (-(t : ℂ)) - Complex.exp (-z * t)) / (1 - Complex.exp (-(t : ℂ)))

/-- For `z = 1/4 + i r/2` the kernel is bounded by `(4 + |r|) e^{1/4} e^{-t/4}`, uniformly in `t > 0`. -/
theorem norm_K_le (r : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖K ((1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I) t‖ ≤ (4 + |r|) * Real.exp (1 / 4) * Real.exp (-t / 4) := by
  set z : ℂ := (1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I with hz
  have hzre : z.re = 1 / 4 := by simp [hz]
  have hznorm : ‖z‖ ≤ 1 / 4 + |r| / 2 := by
    calc ‖z‖ ≤ ‖(1 / 4 : ℂ)‖ + ‖((r / 2 : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 1 / 4 + |r| / 2 := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div]
        simp
  have hden : 0 < 1 - Real.exp (-t) := by
    have := Real.exp_lt_exp.2 (by linarith : -t < 0)
    rw [Real.exp_zero] at this
    linarith
  have hdenC : ‖1 - Complex.exp (-(t : ℂ))‖ = 1 - Real.exp (-t) := by
    have : (1 : ℂ) - Complex.exp (-(t : ℂ)) = ((1 - Real.exp (-t) : ℝ) : ℂ) := by
      push_cast
      rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
    rw [this, Complex.norm_real, Real.norm_of_nonneg hden.le]
  have hbase : 1 ≤ Real.exp (1 / 4) * Real.exp (-t / 4) ∨ 1 ≤ t := by
    by_cases h1 : t < 1
    · left
      rw [← Real.exp_add]
      apply Real.one_le_exp
      linarith
    · right; linarith
  unfold K
  rw [norm_div, hdenC]
  rcases le_or_gt 1 t with h1 | h1
  · -- large t
    have hnum : ‖Complex.exp (-(t : ℂ)) - Complex.exp (-z * t)‖ ≤ 2 * Real.exp (-t / 4) := by
      refine (norm_sub_le _ _).trans ?_
      have e1 : ‖Complex.exp (-(t : ℂ))‖ = Real.exp (-t) := by
        rw [Complex.norm_exp]; simp
      have e2 : ‖Complex.exp (-z * t)‖ = Real.exp (-t / 4) := by
        rw [Complex.norm_exp]
        congr 1
        simp [hzre]
        ring
      rw [e1, e2]
      have : Real.exp (-t) ≤ Real.exp (-t / 4) := Real.exp_le_exp.2 (by linarith)
      linarith
    have hd2 : 1 / 2 ≤ 1 - Real.exp (-t) := by
      have h2 : Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
      have h3 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg]
        have : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ)
          linarith
        rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith
      linarith
    rw [div_le_iff₀ hden]
    have he : 1 ≤ Real.exp (1 / 4) := Real.one_le_exp (by norm_num)
    have hr : 0 ≤ |r| := abs_nonneg r
    have hep : 0 < Real.exp (-t / 4) := Real.exp_pos _
    have hA : 4 ≤ (4 + |r|) * Real.exp (1 / 4) := by nlinarith
    have h5 : 4 * Real.exp (-t / 4) * (1 / 2) ≤
        (4 + |r|) * Real.exp (1 / 4) * Real.exp (-t / 4) * (1 - Real.exp (-t)) := by
      have h6 : 4 * Real.exp (-t / 4) ≤ (4 + |r|) * Real.exp (1 / 4) * Real.exp (-t / 4) :=
        mul_le_mul_of_nonneg_right hA hep.le
      calc 4 * Real.exp (-t / 4) * (1 / 2) ≤
          (4 + |r|) * Real.exp (1 / 4) * Real.exp (-t / 4) * (1 / 2) := by gcongr
        _ ≤ _ := by gcongr
    linarith
  · -- small t
    have hnum : ‖Complex.exp (-(t : ℂ)) - Complex.exp (-z * t)‖ ≤
        ‖z‖ * t + (1 - Real.exp (-t)) := by
      have e : Complex.exp (-(t : ℂ)) - Complex.exp (-z * t) =
          (1 - Complex.exp (-z * t)) - (1 - Complex.exp (-(t : ℂ))) := by ring
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have h2 : ‖1 - Complex.exp (-z * t)‖ ≤ ‖z‖ * t := by
        have := GppDigammaIntegral.norm_one_sub_exp_neg_le (w := z * t) (by simpa [hzre] using by positivity)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le] at this
        simpa [neg_mul] using this
      rw [hdenC]
      linarith
    have hd2 : t / 2 ≤ 1 - Real.exp (-t) := by
      have h3 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
      have h4 : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
      have h5 : Real.exp (-t) ≤ 1 - t / 2 := by
        rw [h4]
        have h6 : (Real.exp t)⁻¹ ≤ (1 + t)⁻¹ := inv_anti₀ (by positivity) h3
        have h7 : (1 + t)⁻¹ ≤ 1 - t / 2 := by
          rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
          nlinarith
        linarith
      linarith
    rw [div_le_iff₀ hden]
    have hAE : 1 ≤ Real.exp (1 / 4) * Real.exp (-t / 4) := by
      rcases hbase with h | h
      · exact h
      · linarith
    have hr : 0 ≤ |r| := abs_nonneg r
    have hD : 0 < 1 - Real.exp (-t) := hden
    have h8 : ‖z‖ * t ≤ (1 / 2 + |r|) * (1 - Real.exp (-t)) := by
      have : t ≤ 2 * (1 - Real.exp (-t)) := by linarith
      calc ‖z‖ * t ≤ ‖z‖ * (2 * (1 - Real.exp (-t))) := by gcongr
        _ ≤ (2 * (1 / 4 + |r| / 2)) * (1 - Real.exp (-t)) := by nlinarith [norm_nonneg z]
        _ = (1 / 2 + |r|) * (1 - Real.exp (-t)) := by ring
    have h9 : (4 + |r|) * 1 * (1 - Real.exp (-t)) ≤
        (4 + |r|) * (Real.exp (1 / 4) * Real.exp (-t / 4)) * (1 - Real.exp (-t)) := by
      gcongr
    nlinarith

/-- The spectral transform on the critical line: `h(r) = ∫ g(u) e^{i r u} du`. -/
noncomputable def hline (g : ℝ → ℝ) (r : ℝ) : ℂ := spectralTransform g ((1 / 2 : ℂ) + r * Complex.I)

theorem hline_eq_fourier {g : ℝ → ℝ} (hg : IsTestFunction g) (r : ℝ) :
    hline g r = (𝓕 (shiftedSchwartz hg (1 / 2))) (-r / (2 * Real.pi)) := by
  have := spectralTransform_eq_fourier hg (1 / 2) r
  simpa [hline] using this

/-- **Fourier inversion for the critical-line transform.**
`g(v) = (1/2π) ∫ e^{-i r v} h(r) dr`. -/
theorem inversion {g : ℝ → ℝ} (hg : IsTestFunction g) (v : ℝ) :
    (g v : ℂ) = (1 / (2 * Real.pi) : ℝ) * ∫ r : ℝ, Complex.exp (-(Complex.I * r * v)) * hline g r := by
  set Gs := shiftedSchwartz hg (1 / 2) with hGs
  have hshift : ∀ u, Gs u = (g u : ℂ) := by
    intro u
    show shifted g (1 / 2) u = _
    unfold shifted
    simp
  have h1 := congrFun (Gs.continuous.fourierInv_fourier_eq Gs.integrable (𝓕 Gs).integrable) v
  rw [Real.fourierInv_eq_fourier_neg] at h1
  rw [Real.fourier_real_eq_integral_exp_smul] at h1
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hF : ∀ ξ : ℝ, Complex.exp (-(Complex.I * ((-2 * Real.pi * ξ : ℝ) : ℂ) * v)) *
      hline g (-2 * Real.pi * ξ) =
      Complex.exp (((-2 * Real.pi * ξ * -v : ℝ) : ℂ) * Complex.I) • 𝓕 (⇑Gs) ξ := by
    intro ξ
    rw [hline_eq_fourier hg, smul_eq_mul]
    have e : -(-2 * Real.pi * ξ) / (2 * Real.pi) = ξ := by field_simp
    rw [e]
    congr 2
    push_cast
    ring
  have hcomp := MeasureTheory.Measure.integral_comp_mul_left
    (fun r : ℝ => Complex.exp (-(Complex.I * (r : ℂ) * v)) * hline g r) (-2 * Real.pi)
  simp only [hF] at hcomp
  rw [h1, hshift] at hcomp
  have habs : |(-2 * Real.pi)⁻¹| = (1 / (2 * Real.pi) : ℝ) := by
    rw [abs_inv, abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos, one_div]
  rw [habs] at hcomp
  rw [hcomp]
  simp only [Complex.real_smul]

/-- `hline g` is continuous and integrable. -/
theorem hline_integrable {g : ℝ → ℝ} (hg : IsTestFunction g) : Integrable (hline g) := by
  have h : hline g = fun r => (𝓕 (shiftedSchwartz hg (1 / 2))) (-r / (2 * Real.pi)) :=
    funext (hline_eq_fourier hg)
  rw [h]
  have hI : Integrable (fun x => (𝓕 (shiftedSchwartz hg (1 / 2))) x) volume :=
    (𝓕 (shiftedSchwartz hg (1 / 2))).integrable
  have := hI.comp_mul_left' (R := -(2 * Real.pi)⁻¹) (by simp [Real.pi_ne_zero])
  refine this.congr (Filter.Eventually.of_forall fun r => ?_)
  show (𝓕 (shiftedSchwartz hg (1 / 2))) (-(2 * Real.pi)⁻¹ * r) = _
  congr 1
  field_simp

theorem hline_continuous {g : ℝ → ℝ} (hg : IsTestFunction g) : Continuous (hline g) := by
  have h : hline g = fun r => (𝓕 (shiftedSchwartz hg (1 / 2))) (-r / (2 * Real.pi)) :=
    funext (hline_eq_fourier hg)
  rw [h]
  exact (𝓕 (shiftedSchwartz hg (1 / 2))).continuous.comp (by fun_prop)

theorem integrable_exp_mul_hline {g : ℝ → ℝ} (hg : IsTestFunction g) (v : ℝ) :
    Integrable (fun r : ℝ => Complex.exp (-(Complex.I * r * v)) * hline g r) := by
  refine (hline_integrable hg).norm.mono' ?_ ?_
  · exact (Continuous.mul (by fun_prop) (hline_continuous hg)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun r => ?_
    rw [norm_mul, Complex.norm_exp]
    have : (-(Complex.I * (r : ℂ) * (v : ℂ))).re = 0 := by simp
    rw [this, Real.exp_zero, one_mul]

/-- The `r`-integral of the kernel against `h` at a fixed height `t > 0`. -/
theorem inner_integral {g : ℝ → ℝ} (hg : IsTestFunction g) {t : ℝ} (ht : 0 < t) :
    ∫ r : ℝ, hline g r * K ((1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I) t =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((Complex.exp (-(t : ℂ)) * (g 0 : ℂ) - Complex.exp (-(t : ℂ) / 4) * (g (t / 2) : ℂ)) /
          (1 - Complex.exp (-(t : ℂ)))) := by
  have hD : (1 - Complex.exp (-(t : ℂ))) ≠ 0 := by
    intro h
    have h1 : Complex.exp (-(t : ℂ)) = 1 := by linear_combination -h
    have hr : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
      rw [Complex.norm_exp]
      have := Real.exp_lt_exp.2 (by linarith : -t < 0)
      simpa using this
    rw [h1] at hr
    simp at hr
  have hK : ∀ r : ℝ, hline g r * K ((1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I) t =
      (Complex.exp (-(t : ℂ)) * hline g r -
        Complex.exp (-(t : ℂ) / 4) * (Complex.exp (-(Complex.I * r * ((t / 2 : ℝ) : ℂ))) * hline g r)) /
        (1 - Complex.exp (-(t : ℂ))) := by
    intro r
    unfold K
    have e : Complex.exp (-((1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I) * t) =
        Complex.exp (-(t : ℂ) / 4) * Complex.exp (-(Complex.I * r * ((t / 2 : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e]
    ring
  simp_rw [hK]
  rw [integral_div, integral_sub ((hline_integrable hg).const_mul _)
    ((integrable_exp_mul_hline hg (t / 2)).const_mul _), integral_const_mul, integral_const_mul]
  have h0 := inversion hg 0
  have h1 := inversion hg (t / 2)
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at h0
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  have i0 : ∫ r : ℝ, hline g r = ((2 * Real.pi : ℝ) : ℂ) * (g 0 : ℂ) := by
    generalize (∫ r : ℝ, hline g r) = J at h0 ⊢
    rw [h0]; push_cast; field_simp
  have i1 : ∫ r : ℝ, Complex.exp (-(Complex.I * r * ((t / 2 : ℝ) : ℂ))) * hline g r =
      ((2 * Real.pi : ℝ) : ℂ) * (g (t / 2) : ℂ) := by
    generalize (∫ r : ℝ, Complex.exp (-(Complex.I * r * ((t / 2 : ℝ) : ℂ))) * hline g r) = J at h1 ⊢
    rw [h1]; push_cast; field_simp
  rw [i0, i1]
  ring

/-- `r ↦ (4 + |r|) ‖h(r)‖` is integrable. -/
theorem integrable_weight_hline {g : ℝ → ℝ} (hg : IsTestFunction g) :
    Integrable (fun r : ℝ => (4 + |r|) * ‖hline g r‖) := by
  obtain ⟨C0, hC0⟩ := spectralTransform_decay hg (1 / 2) 0
  obtain ⟨C3, hC3⟩ := spectralTransform_decay hg (1 / 2) 3
  have hb : ∀ r : ℝ, (4 + |r|) * ‖hline g r‖ ≤ (20 * (|C0| + |C3|)) * (1 / (1 + r ^ 2)) := by
    intro r
    have h0 := hC0 r
    have h3 := hC3 r
    have e : (((1 / 2 : ℝ) : ℂ) + (r : ℂ) * Complex.I) = (1 / 2 : ℂ) + (r : ℂ) * Complex.I := by
      push_cast; ring
    rw [e] at h0 h3
    change |r| ^ 0 * ‖hline g r‖ ≤ C0 at h0
    change |r| ^ 3 * ‖hline g r‖ ≤ C3 at h3
    simp only [pow_zero, one_mul] at h0
    have hh : 0 ≤ ‖hline g r‖ := norm_nonneg _
    have ha : 0 ≤ |r| := abs_nonneg r
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    have hsq : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
    rw [hsq]
    have hC : ‖hline g r‖ * (1 + |r| ^ 3) ≤ |C0| + |C3| := by
      have := le_abs_self C0
      have := le_abs_self C3
      nlinarith
    nlinarith [mul_nonneg hh ha, mul_nonneg (mul_nonneg hh ha) ha, mul_nonneg hh (sq_nonneg |r|),
      mul_nonneg (mul_nonneg hh ha) (sq_nonneg |r|), hC]
  have hmaj : Integrable (fun r : ℝ => (20 * (|C0| + |C3|)) * (1 / (1 + r ^ 2))) := by
    simpa [one_div] using integrable_inv_one_add_sq.const_mul (20 * (|C0| + |C3|))
  refine Integrable.mono' hmaj ?_ ?_
  · exact (Continuous.mul (by fun_prop) (hline_continuous hg).norm).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun r => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact hb r

/-- Joint integrability of `h(r) K(z_r, t)` over `ℝ × (0, ∞)`. -/
theorem integrable_prod {g : ℝ → ℝ} (hg : IsTestFunction g) :
    Integrable (fun p : ℝ × ℝ => hline g p.1 * K ((1 / 4 : ℂ) + (p.1 / 2 : ℝ) * Complex.I) p.2)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hf : Integrable (fun r : ℝ => (4 + |r|) * ‖hline g r‖ * Real.exp (1 / 4)) :=
    (integrable_weight_hline hg).mul_const _
  have hgt : Integrable (fun t : ℝ => Real.exp (-t / 4)) (volume.restrict (Ioi (0 : ℝ))) := by
    have h : IntegrableOn (fun t : ℝ => ‖Complex.exp (-(1 / 4 : ℂ) * t)‖) (Ioi 0) :=
      (GppDigammaIntegral.integrableOn_exp_neg (a := (1 / 4 : ℂ)) (by simp)).norm
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Complex.norm_exp]
    congr 1
    simp
    ring
  have hM := hf.mul_prod hgt
  refine hM.mono' ?_ ?_
  · -- measurability
    have hc : Continuous (hline g) := hline_continuous hg
    have h1 : Measurable (fun p : ℝ × ℝ => hline g p.1) := hc.measurable.comp measurable_fst
    have h2 : Measurable (fun p : ℝ × ℝ =>
        K ((1 / 4 : ℂ) + (p.1 / 2 : ℝ) * Complex.I) p.2) := by
      unfold K
      refine Measurable.div ?_ ?_
      · refine Measurable.sub (by fun_prop) ?_
        exact Complex.measurable_exp.comp (by fun_prop)
      · exact measurable_const.sub (Complex.measurable_exp.comp (by fun_prop))
    exact (h1.mul h2).aestronglyMeasurable
  · rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), Measure.prod_restrict,
      Measure.restrict_univ]
    rw [ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ioi)]
    refine Filter.Eventually.of_forall fun p hp => ?_
    have ht : 0 < p.2 := hp.2
    rw [norm_mul]
    have := norm_K_le p.1 ht
    calc ‖hline g p.1‖ * ‖K ((1 / 4 : ℂ) + (p.1 / 2 : ℝ) * Complex.I) p.2‖
        ≤ ‖hline g p.1‖ * ((4 + |p.1|) * Real.exp (1 / 4) * Real.exp (-p.2 / 4)) := by gcongr
      _ = (4 + |p.1|) * ‖hline g p.1‖ * Real.exp (1 / 4) * Real.exp (-p.2 / 4) := by ring

/-- **The Archimedean term from the digamma line integral.** For every test function `g`,
`(1/2π) ∫ h(r) ψ(1/4 + i r/2) dr = archimedeanTerm g + g(0) log π`, where
`h(r) = ĝ(1/2 + i r)`. (For even `g` this is the classical
`archimedeanTerm g = -g(0) log π + (1/2π) ∫ h(r) Re ψ(1/4 + i r/2) dr`.) -/
theorem archimedean_identification {g : ℝ → ℝ} (hg : IsTestFunction g) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ, hline g r * Complex.digamma ((1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I) =
      ((GppArchimedeanFloor.archimedeanTerm g + g 0 * Real.log Real.pi : ℝ) : ℂ) := by
  set z : ℝ → ℂ := fun r => (1 / 4 : ℂ) + (r / 2 : ℝ) * Complex.I with hzdef
  have hzre : ∀ r, 0 < (z r).re := fun r => by simp [hzdef]
  have hdig : ∀ r, Complex.digamma (z r) = -(Real.eulerMascheroniConstant : ℂ) +
      ∫ t : ℝ in Ioi 0, K (z r) t := fun r => GppDigammaIntegral.digamma_eq_integral (hzre r)
  have hInt := integrable_prod hg
  -- the `r`-integrable inner integral
  have hinner : Integrable (fun r : ℝ => ∫ t : ℝ in Ioi 0, hline g r * K (z r) t) := hInt.integral_prod_left
  have hpull : ∀ r : ℝ, ∫ t : ℝ in Ioi 0, hline g r * K (z r) t =
      hline g r * ∫ t : ℝ in Ioi 0, K (z r) t := fun r => integral_const_mul _ _
  have hstep1 : ∫ r : ℝ, hline g r * Complex.digamma (z r) =
      -(Real.eulerMascheroniConstant : ℂ) * (∫ r : ℝ, hline g r) +
        (∫ r : ℝ, ∫ t : ℝ in Ioi 0, hline g r * K (z r) t) := by
    have e : ∀ r : ℝ, hline g r * Complex.digamma (z r) =
        -(Real.eulerMascheroniConstant : ℂ) * hline g r + ∫ t : ℝ in Ioi 0, hline g r * K (z r) t := by
      intro r
      rw [hdig r, hpull r]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall e),
      integral_add ((hline_integrable hg).const_mul _) hinner, integral_const_mul]
  have hswap : ∫ r : ℝ, ∫ t : ℝ in Ioi 0, hline g r * K (z r) t =
      ∫ t : ℝ in Ioi 0, ∫ r : ℝ, hline g r * K (z r) t :=
    MeasureTheory.integral_integral_swap hInt
  sorry

end GppArchimedeanId
