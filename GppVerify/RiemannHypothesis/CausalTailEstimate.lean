/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statement from Codex / GPT, audited by Turbo)
-/
import Mathlib.Tactic
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Causal tail estimate (Part A of the causal proof of `EnergyZeroInequality`)

**Unconditional; this is a lemma, not RH.** Part A of the four-part formalization of Codex's causal
proof (`causal_zero_bound.md`, Turbo-audited) of `GppSparseCutoff.EnergyZeroInequality`.

Setting. `k`, `h`, `B : ℝ → ℝ` measurable, `k ∈ L¹(0,∞)`, `h ∈ L²(0,∞)`, `B ∈ L²(0,L]`, and
`h = k ⋆ (B 1_{(0,L]})` on `(0, L]` where `k₀ = k 1_{(0,∞)}` and `⋆` is the real convolution on `ℝ`
(`rconv`). If the Laplace transform `∫₀^∞ e^{-rt} k(t) dt` vanishes at some `r` with `d = Re r > 0`,
then

`√(2d) · e^{dL} · |∫₀^∞ e^{-rt} h(t) dt| ≤ ‖h‖_{L²(0,∞)} + ‖k‖_{L¹(0,∞)} · ‖B‖_{L²(0,L]}`.

Proof (as in the note): the truncation `h_L = k₀ ⋆ B₀` has transform `k̂(r) B̂₀(r) = 0`
(`lap_rconv`, Mathlib `integral_convolution`), and `h = h_L` on `(0, L]`, so
`ĥ(r) = ∫_L^∞ e^{-rt}(h − h_L)`. Each tail is bounded by Cauchy–Schwarz against `e^{-dt}`
(`tail_sq_le`), and `‖h_L‖₂ ≤ ‖k‖₁‖B₀‖₂` is Young's inequality, proved here (`lintegral_sq_conv_le`;
Mathlib at this pin has no `L¹ ∗ L²` bound).

What this is **not**: the kernels `g_j`, `w`, `Z`, `k` and the identity `h = k ⋆ B` (Part B), the
transforms at a zero `ĥ(r) = (r−½)/(1+r)⁴`, `k̂(r) = 0` (Part C) and the norm bounds `‖Z‖₂ ≤ 9`,
`‖k‖₁ ≤ 18` (Part D) are not in this file.
-/

open MeasureTheory ENNReal Set

namespace GppCausalTail


/-- Cauchy–Schwarz in `ℝ≥0∞`. -/
theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {u v : α → ℝ≥0∞}
    (hu : AEMeasurable u μ) (hv : AEMeasurable v μ) :
    (∫⁻ a, u a * v a ∂μ) ^ 2 ≤ (∫⁻ a, u a ^ 2 ∂μ) * ∫⁻ a, v a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hu hv
  have h2 : (∫⁻ a, u a * v a ∂μ) ^ 2 ≤
      ((∫⁻ a, u a ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) * (∫⁻ a, v a ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ))) ^ 2 := by
    gcongr
    simpa using h
  refine h2.trans (le_of_eq ?_)
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  simp

/-- The decaying weight: `∫_L^∞ e^{-2dt} dt = e^{-2dL}/(2d)`, as an `ℝ≥0∞` integral of squares. -/
theorem lintegral_weight_sq (d L : ℝ) (hd : 0 < d) :
    ∫⁻ t in Ioi L, ENNReal.ofReal (Real.exp (-(d * t))) ^ 2 =
      ENNReal.ofReal (Real.exp (-(2 * d * L)) / (2 * d)) := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp ((-(2 * d)) * t)) (Ioi L) :=
    integrableOn_exp_mul_Ioi (by linarith) L
  have h1 : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-(d * t))) ^ 2 =
      ENNReal.ofReal (Real.exp ((-(2 * d)) * t)) := by
    intro t
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2
    push_cast; ring
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)]
  rw [integral_exp_mul_Ioi (by linarith)]
  congr 1
  have h2d : (2 * d) ≠ 0 := by positivity
  field_simp

/-- Weighted `L²`-to-`L¹` Cauchy–Schwarz in `ℝ≥0∞`: with `e^{-dt}` weight on `(L, ∞)`. -/
theorem lintegral_exp_mul_sq_le (g : ℝ → ℝ) (hg : AEMeasurable g) (d : ℝ) (hd : 0 < d) (L : ℝ) :
    (∫⁻ t in Ioi L, ENNReal.ofReal (Real.exp (-(d * t))) * ‖g t‖ₑ) ^ 2 ≤
      (∫⁻ t in Ioi L, ‖g t‖ₑ ^ 2) * ENNReal.ofReal (Real.exp (-(2 * d * L)) / (2 * d)) := by
  have hum : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-(d * t))) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg).ennreal_ofReal
  calc (∫⁻ t in Ioi L, ENNReal.ofReal (Real.exp (-(d * t))) * ‖g t‖ₑ) ^ 2
      ≤ (∫⁻ t in Ioi L, ENNReal.ofReal (Real.exp (-(d * t))) ^ 2) *
          ∫⁻ t in Ioi L, ‖g t‖ₑ ^ 2 :=
        lintegral_mul_sq_le _ hum.aemeasurable hg.enorm.restrict
    _ = _ := by rw [lintegral_weight_sq _ _ hd, mul_comm]

theorem enorm_exp_neg_mul (r : ℂ) (t : ℝ) :
    ‖Complex.exp (-r * (t : ℂ))‖ₑ = ENNReal.ofReal (Real.exp (-(r.re * t))) := by
  rw [← ofReal_norm, Complex.norm_exp]
  congr 2
  simp

theorem enorm_exp_mul_real (r : ℂ) (g : ℝ → ℝ) (t : ℝ) :
    ‖Complex.exp (-r * (t : ℂ)) * (g t : ℂ)‖ₑ =
      ENNReal.ofReal (Real.exp (-(r.re * t))) * ‖g t‖ₑ := by
  rw [enorm_mul, enorm_exp_neg_mul]
  congr 1
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]

/-- Tail Cauchy–Schwarz: `|∫_L^∞ e^{-rt} g(t) dt|² ≤ (∫_L^∞ g²) · e^{-2dL}/(2d)`, `d = Re r > 0`. -/
theorem tail_sq_le (g : ℝ → ℝ) (hg : AEMeasurable g) (r : ℂ) (hd : 0 < r.re) (L : ℝ) :
    ‖∫ t in Ioi L, Complex.exp (-r * (t : ℂ)) * (g t : ℂ)‖ₑ ^ 2 ≤
      (∫⁻ t in Ioi L, ‖g t‖ₑ ^ 2) * ENNReal.ofReal (Real.exp (-(2 * r.re * L)) / (2 * r.re)) := by
  have h1 : ‖∫ t in Ioi L, Complex.exp (-r * (t : ℂ)) * (g t : ℂ)‖ₑ ≤
      ∫⁻ t in Ioi L, ENNReal.ofReal (Real.exp (-(r.re * t))) * ‖g t‖ₑ :=
    (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun t =>
      enorm_exp_mul_real r g t))
  exact (pow_le_pow_left' h1 2).trans (lintegral_exp_mul_sq_le g hg r.re hd L)

/-- Integrability of `e^{-rt} g(t)` on `(L, ∞)` for `g ∈ L²(L, ∞)`. -/
theorem integrableOn_exp_mul_of_sq (g : ℝ → ℝ) (hg : AEMeasurable g) (r : ℂ) (hd : 0 < r.re)
    (L : ℝ) (hfin : ∫⁻ t in Ioi L, ‖g t‖ₑ ^ 2 < ⊤) :
    IntegrableOn (fun t : ℝ => Complex.exp (-r * (t : ℂ)) * (g t : ℂ)) (Ioi L) := by
  refine ⟨?_, ?_⟩
  · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hg.aestronglyMeasurable).restrict
  · unfold HasFiniteIntegral
    simp_rw [enorm_exp_mul_real]
    have := lintegral_exp_mul_sq_le g hg r.re hd L
    have hlt : (∫⁻ t in Ioi L, ENNReal.ofReal (Real.exp (-(r.re * t))) * ‖g t‖ₑ) ^ 2 < ⊤ :=
      this.trans_lt (ENNReal.mul_lt_top hfin ENNReal.ofReal_lt_top)
    rcases ENNReal.pow_lt_top_iff.1 hlt with h | h
    · exact h
    · norm_num at h

/-- Weighted Cauchy–Schwarz: `(∫ a b)² ≤ (∫ a)(∫ a b²)`. -/
theorem lintegral_weighted_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {a b : α → ℝ≥0∞}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    (∫⁻ s, a s * b s ∂μ) ^ 2 ≤ (∫⁻ s, a s ∂μ) * ∫⁻ s, a s * b s ^ 2 ∂μ := by
  have hu : AEMeasurable (fun s => a s ^ (1/2 : ℝ)) μ := ha.pow_const _
  have hv : AEMeasurable (fun s => a s ^ (1/2 : ℝ) * b s) μ := hu.mul hb
  have h := lintegral_mul_sq_le μ hu hv
  have e1 : ∀ s, a s ^ (1/2 : ℝ) * (a s ^ (1/2 : ℝ) * b s) = a s * b s := by
    intro s
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ s, (a s ^ (1/2 : ℝ)) ^ 2 = a s := by
    intro s
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have e3 : ∀ s, (a s ^ (1/2 : ℝ) * b s) ^ 2 = a s * b s ^ 2 := by
    intro s
    rw [mul_pow, e2]
  simp only [e1, e2, e3] at h
  exact h

/-- Young's inequality, `L¹ ∗ L² → L²`, in `ℝ≥0∞` form with the convolution of absolute values. -/
theorem lintegral_sq_conv_le (k f : ℝ → ℝ) (hk : Measurable k) (hf : Measurable f) :
    ∫⁻ t, (∫⁻ s, ‖k s‖ₑ * ‖f (t - s)‖ₑ) ^ 2 ≤
      (∫⁻ s, ‖k s‖ₑ) ^ 2 * ∫⁻ t, ‖f t‖ₑ ^ 2 := by
  set K := ∫⁻ s, ‖k s‖ₑ with hK
  have hkm : Measurable fun s => ‖k s‖ₑ := hk.enorm
  have step : ∀ t, (∫⁻ s, ‖k s‖ₑ * ‖f (t - s)‖ₑ) ^ 2 ≤
      K * ∫⁻ s, ‖k s‖ₑ * ‖f (t - s)‖ₑ ^ 2 := fun t =>
    lintegral_weighted_sq_le volume hkm.aemeasurable
      ((hf.comp (measurable_const.sub measurable_id)).enorm.aemeasurable)
  have hG : Measurable (fun p : ℝ × ℝ => ‖k p.2‖ₑ * ‖f (p.1 - p.2)‖ₑ ^ 2) := by
    have h1 : Measurable fun p : ℝ × ℝ => ‖k p.2‖ₑ := (hk.comp measurable_snd).enorm
    have h2 : Measurable fun p : ℝ × ℝ => ‖f (p.1 - p.2)‖ₑ :=
      (hf.comp (measurable_fst.sub measurable_snd)).enorm
    exact h1.mul (h2.pow_const 2)
  calc ∫⁻ t, (∫⁻ s, ‖k s‖ₑ * ‖f (t - s)‖ₑ) ^ 2
      ≤ ∫⁻ t, K * ∫⁻ s, ‖k s‖ₑ * ‖f (t - s)‖ₑ ^ 2 := lintegral_mono step
    _ = K * ∫⁻ t, ∫⁻ s, ‖k s‖ₑ * ‖f (t - s)‖ₑ ^ 2 := by
        rw [lintegral_const_mul]
        exact hG.lintegral_prod_right'
    _ = K * ∫⁻ s, ‖k s‖ₑ * ∫⁻ t, ‖f (t - s)‖ₑ ^ 2 := by
        congr 1
        rw [lintegral_lintegral_swap hG.aemeasurable]
        refine lintegral_congr fun s => ?_
        rw [lintegral_const_mul]
        exact (hf.comp (measurable_id.sub measurable_const)).enorm.pow_const 2
    _ = K * ∫⁻ s, ‖k s‖ₑ * ∫⁻ t, ‖f t‖ₑ ^ 2 := by
        congr 1
        refine lintegral_congr fun s => ?_
        rw [lintegral_sub_right_eq_self (fun t => ‖f t‖ₑ ^ 2) s]
    _ = K ^ 2 * ∫⁻ t, ‖f t‖ₑ ^ 2 := by
        rw [lintegral_mul_const _ hkm, ← hK]
        ring



/-- Real convolution `(f ⋆ g)(t) = ∫ s, f s * g (t - s)`. -/
noncomputable abbrev rconv (f g : ℝ → ℝ) : ℝ → ℝ :=
  convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume

theorem rconv_apply (f g : ℝ → ℝ) (t : ℝ) : rconv f g t = ∫ s, f s * g (t - s) := by
  simp [rconv, convolution_def]

theorem rconv_nonpos (f g : ℝ → ℝ) (hf : ∀ s, s ≤ 0 → f s = 0) (hg : ∀ s, s ≤ 0 → g s = 0)
    {t : ℝ} (ht : t ≤ 0) : rconv f g t = 0 := by
  rw [rconv_apply]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : s ≤ 0
  · simp [hf s hs]
  · have : t - s ≤ 0 := by linarith [not_le.1 hs]
    simp [hg _ this]

/-- Weighted (complex) function `e^{-rt} f(t)`. -/
noncomputable def wt (r : ℂ) (f : ℝ → ℝ) (t : ℝ) : ℂ := Complex.exp (-r * (t : ℂ)) * (f t : ℂ)

theorem integrable_wt (r : ℂ) (hd : 0 < r.re) (f : ℝ → ℝ) (hf : Integrable f)
    (hf0 : ∀ s, s ≤ 0 → f s = 0) : Integrable (wt r f) := by
  refine Integrable.mono' hf.norm ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  · unfold wt
    rw [norm_mul, Complex.norm_exp, Complex.norm_real]
    by_cases ht : t ≤ 0
    · simp [hf0 t ht]
    · have : Real.exp ((-r * (t : ℂ)).re) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
          Complex.ofReal_im]
        nlinarith [not_le.1 ht]
      calc Real.exp ((-r * (t : ℂ)).re) * ‖f t‖ ≤ 1 * ‖f t‖ := by gcongr
        _ = ‖f t‖ := one_mul _

theorem wt_conv (r : ℂ) (f g : ℝ → ℝ) (t : ℝ) :
    wt r (rconv f g) t =
      convolution (wt r f) (wt r g) (ContinuousLinearMap.mul ℂ ℂ) volume t := by
  rw [convolution_def]
  unfold wt
  rw [rconv_apply, ← integral_complex_ofReal, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [ContinuousLinearMap.mul_apply', Complex.ofReal_mul]
  have : Complex.exp (-r * (t : ℂ)) =
      Complex.exp (-r * (s : ℂ)) * Complex.exp (-r * ((t - s : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [this]; ring

theorem wt_eq_zero_of_nonpos (r : ℂ) (f : ℝ → ℝ) (hf0 : ∀ s, s ≤ 0 → f s = 0) {t : ℝ}
    (ht : t ≤ 0) : wt r f t = 0 := by
  simp [wt, hf0 t ht]

/-- The Laplace transform of a causal convolution is the product of the transforms. -/
theorem lap_rconv (r : ℂ) (hd : 0 < r.re) (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hf0 : ∀ s, s ≤ 0 → f s = 0) (hg0 : ∀ s, s ≤ 0 → g s = 0) :
    ∫ t in Ioi 0, wt r (rconv f g) t =
      (∫ t in Ioi 0, wt r f t) * ∫ t in Ioi 0, wt r g t := by
  have hF := integrable_wt r hd f hf hf0
  have hG := integrable_wt r hd g hg hg0
  have hz : ∀ (u : ℝ → ℝ), (∀ s, s ≤ 0 → u s = 0) → ∫ t in Ioi 0, wt r u t = ∫ t, wt r u t := by
    intro u hu
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
      wt_eq_zero_of_nonpos r u hu (not_lt.1 ht)
  rw [hz f hf0, hz g hg0, hz (rconv f g) (fun s hs => rconv_nonpos f g hf0 hg0 hs)]
  have : (fun t => wt r (rconv f g) t) =
      convolution (wt r f) (wt r g) (ContinuousLinearMap.mul ℂ ℂ) volume := by
    funext t; exact wt_conv r f g t
  rw [this, integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hF hG]
  simp



theorem lintegral_sq_rconv_le (k f : ℝ → ℝ) (hk : Measurable k) (hf : Measurable f) :
    ∫⁻ t, ‖rconv k f t‖ₑ ^ 2 ≤ (∫⁻ s, ‖k s‖ₑ) ^ 2 * ∫⁻ t, ‖f t‖ₑ ^ 2 := by
  refine le_trans (lintegral_mono fun t => ?_) (lintegral_sq_conv_le k f hk hf)
  have h : ‖rconv k f t‖ₑ ≤ ∫⁻ s, ‖k s‖ₑ * ‖f (t - s)‖ₑ := by
    rw [rconv_apply]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp [enorm_mul]
  gcongr

/-- `∫⁻ ‖g‖ₑ² = ofReal ∫ g²` when `g²` is integrable. -/
theorem lintegral_enorm_sq_eq (s : Set ℝ) (g : ℝ → ℝ) (hg : IntegrableOn (fun t => g t ^ 2) s) :
    ∫⁻ t in s, ‖g t‖ₑ ^ 2 = ENNReal.ofReal (∫ t in s, g t ^ 2) := by
  rw [ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall fun t => sq_nonneg _)]
  refine lintegral_congr fun t => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

theorem lintegral_enorm_sq_lt_top (s : Set ℝ) (g : ℝ → ℝ) (hg : IntegrableOn (fun t => g t ^ 2) s) :
    ∫⁻ t in s, ‖g t‖ₑ ^ 2 < ⊤ := by
  rw [lintegral_enorm_sq_eq s g hg]; exact ENNReal.ofReal_lt_top


theorem integrableOn_of_sq (B : ℝ → ℝ) (hB : Measurable B) (L : ℝ)
    (hB2 : IntegrableOn (fun t => B t ^ 2) (Ioc 0 L)) : IntegrableOn B (Ioc 0 L) := by
  have h1 : IntegrableOn (fun t : ℝ => 1 + B t ^ 2) (Ioc 0 L) :=
    (integrableOn_const (by simp)).add hB2
  refine Integrable.mono' h1 hB.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (B t), sq_abs (B t), sq_nonneg (|B t| - 1)]

/-- **Part A — the causal tail estimate.** -/
theorem causal_tail_estimate (k h B : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (r : ℂ) (hd : 0 < r.re)
    (hk : Measurable k) (hh : Measurable h) (hB : Measurable B)
    (hk1 : IntegrableOn k (Ioi 0)) (hh2 : IntegrableOn (fun t => h t ^ 2) (Ioi 0))
    (hB2 : IntegrableOn (fun t => B t ^ 2) (Ioc 0 L))
    (hconv : ∀ t ∈ Ioc 0 L, h t = rconv ((Ioi 0).indicator k) ((Ioc 0 L).indicator B) t)
    (hkr : ∫ t : ℝ in Ioi 0, Complex.exp (-r * (t : ℂ)) * (k t : ℂ) = 0) :
    Real.sqrt (2 * r.re) * Real.exp (r.re * L) *
        ‖∫ t : ℝ in Ioi 0, Complex.exp (-r * (t : ℂ)) * (h t : ℂ)‖ ≤
      Real.sqrt (∫ t in Ioi 0, h t ^ 2) +
        (∫ s in Ioi 0, |k s|) * Real.sqrt (∫ t in Ioc 0 L, B t ^ 2) := by
  set k₀ : ℝ → ℝ := (Ioi 0).indicator k with hk₀
  set B₀ : ℝ → ℝ := (Ioc 0 L).indicator B with hB₀
  have hk₀m : Measurable k₀ := hk.indicator measurableSet_Ioi
  have hB₀m : Measurable B₀ := hB.indicator measurableSet_Ioc
  have hk₀0 : ∀ s, s ≤ 0 → k₀ s = 0 := fun s hs =>
    indicator_of_notMem (by simpa using hs) _
  have hB₀0 : ∀ s, s ≤ 0 → B₀ s = 0 := fun s hs =>
    indicator_of_notMem (by simp; intro h; linarith) _
  have hk₀int : Integrable k₀ := (integrable_indicator_iff measurableSet_Ioi).2 hk1
  have hB₀int : Integrable B₀ :=
    (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_of_sq B hB L hB2)
  set hLf : ℝ → ℝ := rconv k₀ B₀ with hLf_def
  have hLint : Integrable hLf :=
    Integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hk₀int hB₀int
  have hLm : AEMeasurable hLf := hLint.aemeasurable
  -- the truncated convolution has vanishing transform at `r`
  have lap0 : ∫ t in Ioi 0, wt r hLf t = 0 := by
    rw [hLf_def, lap_rconv r hd k₀ B₀ hk₀int hB₀int hk₀0 hB₀0]
    have : ∫ t in Ioi 0, wt r k₀ t = 0 := by
      rw [← hkr]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      simp only [wt, hk₀, indicator_of_mem ht]
    rw [this, zero_mul]
  have hhI : IntegrableOn (wt r h) (Ioi 0) :=
    integrableOn_exp_mul_of_sq h hh.aemeasurable r hd 0 (lintegral_enorm_sq_lt_top _ h hh2)
  have hLI : IntegrableOn (wt r hLf) (Ioi 0) :=
    (integrable_wt r hd hLf hLint (fun s hs => rconv_nonpos k₀ B₀ hk₀0 hB₀0 hs)).integrableOn
  have hdisj : Disjoint (Ioc (0:ℝ) L) (Ioi L) :=
    Set.disjoint_left.2 fun x hx hx' => not_lt.2 hx.2 hx'
  have split : ∀ u : ℝ → ℂ, IntegrableOn u (Ioi 0) →
      ∫ t in Ioi 0, u t = (∫ t in Ioc 0 L, u t) + ∫ t in Ioi L, u t := by
    intro u hu
    rw [← setIntegral_union hdisj measurableSet_Ioi (hu.mono_set Ioc_subset_Ioi_self)
      (hu.mono_set (Ioi_subset_Ioi hL)), Ioc_union_Ioi_eq_Ioi hL]
  have e3 : ∫ t in Ioc 0 L, wt r h t = ∫ t in Ioc 0 L, wt r hLf t := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    simp only [wt]
    rw [hconv t ht]
  have hsplit : ∫ t in Ioi 0, wt r h t =
      (∫ t in Ioi L, wt r h t) - ∫ t in Ioi L, wt r hLf t := by
    have a1 := split _ hhI
    have a2 := split _ hLI
    rw [lap0] at a2
    linear_combination a1 + (-1) * a2 + e3
  -- quantities
  set d := r.re with hd_def
  set hh_r : ℝ := ∫ t in Ioi 0, h t ^ 2 with hhr
  set K_r : ℝ := ∫ s in Ioi 0, |k s| with hKr
  set F_r : ℝ := ∫ t in Ioc 0 L, B t ^ 2 with hFr
  set e_r : ℝ := Real.exp (-(2 * d * L)) / (2 * d) with her
  have hh_nn : 0 ≤ hh_r := setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  have hK_nn : 0 ≤ K_r := setIntegral_nonneg measurableSet_Ioi fun t _ => abs_nonneg _
  have hF_nn : 0 ≤ F_r := setIntegral_nonneg measurableSet_Ioc fun t _ => sq_nonneg _
  have he_nn : 0 ≤ e_r := by positivity
  -- ENNReal bounds
  have hH1 : ∫⁻ t in Ioi L, ‖h t‖ₑ ^ 2 ≤ ENNReal.ofReal hh_r := by
    rw [← lintegral_enorm_sq_eq _ h hh2]
    exact lintegral_mono_set (Ioi_subset_Ioi hL)
  have hKe : ∫⁻ s, ‖k₀ s‖ₑ = ENNReal.ofReal K_r := by
    have : ∀ s, ‖k₀ s‖ₑ = (Ioi (0:ℝ)).indicator (fun s => ‖k s‖ₑ) s := fun s => by
      by_cases hs : s ∈ Ioi (0:ℝ) <;> simp [hk₀, hs]
    simp_rw [this]
    rw [lintegral_indicator measurableSet_Ioi, hKr]
    simp_rw [← Real.norm_eq_abs]
    exact (ofReal_integral_norm_eq_lintegral_enorm hk1).symm
  have hFe : ∫⁻ t, ‖B₀ t‖ₑ ^ 2 = ENNReal.ofReal F_r := by
    have : ∀ t, ‖B₀ t‖ₑ ^ 2 = (Ioc (0:ℝ) L).indicator (fun t => ‖B t‖ₑ ^ 2) t := fun t => by
      by_cases ht : t ∈ Ioc (0:ℝ) L <;> simp [hB₀, ht]
    simp_rw [this]
    rw [lintegral_indicator measurableSet_Ioc]
    exact lintegral_enorm_sq_eq _ B hB2
  have hH2 : ∫⁻ t in Ioi L, ‖hLf t‖ₑ ^ 2 ≤ ENNReal.ofReal K_r ^ 2 * ENNReal.ofReal F_r := by
    calc ∫⁻ t in Ioi L, ‖hLf t‖ₑ ^ 2 ≤ ∫⁻ t, ‖hLf t‖ₑ ^ 2 := setLIntegral_le_lintegral _ _
      _ ≤ (∫⁻ s, ‖k₀ s‖ₑ) ^ 2 * ∫⁻ t, ‖B₀ t‖ₑ ^ 2 := lintegral_sq_rconv_le k₀ B₀ hk₀m hB₀m
      _ = _ := by rw [hKe, hFe]
  have T1 := tail_sq_le h hh.aemeasurable r hd L
  have T2 := tail_sq_le hLf hLm r hd L
  set a : ℝ := ‖∫ t : ℝ in Ioi L, wt r h t‖ with ha_def
  set b : ℝ := ‖∫ t : ℝ in Ioi L, wt r hLf t‖ with hb_def
  have hEe : ENNReal.ofReal (Real.exp (-(2 * r.re * L)) / (2 * r.re)) = ENNReal.ofReal e_r := rfl
  have Ta : a ^ 2 ≤ hh_r * e_r := by
    have h1 := T1.trans (mul_le_mul' hH1 le_rfl)
    rw [hEe, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul hh_nn,
      ENNReal.ofReal_le_ofReal_iff (mul_nonneg hh_nn he_nn)] at h1
    exact h1
  have Tb : b ^ 2 ≤ K_r ^ 2 * F_r * e_r := by
    have h1 := T2.trans (mul_le_mul' hH2 le_rfl)
    rw [hEe, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow hK_nn,
      ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hF_nn),
      ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (sq_nonneg _) hF_nn) he_nn)] at h1
    exact h1
  have hsq : Real.sqrt e_r = Real.exp (-(d * L)) / Real.sqrt (2 * d) := by
    rw [her, Real.sqrt_div (Real.exp_pos _).le]
    congr 1
    have : Real.exp (-(2 * d * L)) = Real.exp (-(d * L)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this, Real.sqrt_sq (Real.exp_pos _).le]
  have hkey : Real.sqrt (2 * d) * Real.exp (d * L) * Real.sqrt e_r = 1 := by
    rw [hsq]
    have h2 : 0 < Real.sqrt (2 * d) := Real.sqrt_pos.2 (by linarith)
    have h3 : Real.exp (d * L) * Real.exp (-(d * L)) = 1 := by
      rw [← Real.exp_add]; simp
    field_simp
    linarith [h3]
  have ha' : a ≤ Real.sqrt hh_r * Real.sqrt e_r := by
    rw [← Real.sqrt_mul hh_nn]
    exact (le_abs_self a).trans (Real.abs_le_sqrt Ta)
  have hb' : b ≤ K_r * Real.sqrt F_r * Real.sqrt e_r := by
    have h0 : 0 ≤ K_r * Real.sqrt F_r * Real.sqrt e_r := by positivity
    refine (sq_le_sq₀ (norm_nonneg _) h0).1 ?_
    calc b ^ 2 ≤ K_r ^ 2 * F_r * e_r := Tb
      _ = (K_r * Real.sqrt F_r * Real.sqrt e_r) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hF_nn, Real.sq_sqrt he_nn]
  have hX : ‖∫ t : ℝ in Ioi 0, Complex.exp (-r * (t : ℂ)) * (h t : ℂ)‖ ≤ a + b := by
    have : ∫ t : ℝ in Ioi 0, Complex.exp (-r * (t : ℂ)) * (h t : ℂ) =
        (∫ t in Ioi L, wt r h t) - ∫ t in Ioi L, wt r hLf t := hsplit
    rw [this]
    exact norm_sub_le _ _
  have hpos : 0 ≤ Real.sqrt (2 * d) * Real.exp (d * L) := by positivity
  calc Real.sqrt (2 * r.re) * Real.exp (r.re * L) *
        ‖∫ t : ℝ in Ioi 0, Complex.exp (-r * (t : ℂ)) * (h t : ℂ)‖
      ≤ Real.sqrt (2 * d) * Real.exp (d * L) * (a + b) := mul_le_mul_of_nonneg_left hX hpos
    _ ≤ Real.sqrt (2 * d) * Real.exp (d * L) *
          ((Real.sqrt hh_r + K_r * Real.sqrt F_r) * Real.sqrt e_r) :=
        mul_le_mul_of_nonneg_left (by nlinarith [ha', hb']) hpos
    _ = Real.sqrt hh_r + K_r * Real.sqrt F_r := by
        have : Real.sqrt (2 * d) * Real.exp (d * L) *
            ((Real.sqrt hh_r + K_r * Real.sqrt F_r) * Real.sqrt e_r) =
            (Real.sqrt hh_r + K_r * Real.sqrt F_r) *
              (Real.sqrt (2 * d) * Real.exp (d * L) * Real.sqrt e_r) := by ring
        rw [this, hkey, mul_one]

end GppCausalTail
