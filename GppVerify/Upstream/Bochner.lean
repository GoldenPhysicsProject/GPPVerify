/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import GppVerify.Upstream.PositiveDefiniteFunction
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Bochner's theorem on `ℝ`

A continuous positive-definite function `φ : ℝ → ℂ` is the characteristic function of a unique
finite measure on `ℝ`.

## Main results

* `Complex.IsPositiveDefinite.exists_measure_charFun_eq`: **Bochner's theorem.** For continuous
  positive-definite `φ` there is a finite measure `μ` with `charFun μ t = φ t` for all `t`.
* `Complex.IsPositiveDefinite.existsUnique_measure_charFun_eq`: the measure is unique.
* `Complex.IsPositiveDefinite.integral_integral_nonneg`: for continuous integrable `g`,
  `0 ≤ ∫ x, ∫ y, conj (g x) * g y * φ (x - y)`.
* `Complex.IsPositiveDefinite.integral_autocorr_mul_nonneg`: the same as the pairing
  `0 ≤ ∫ u, (∫ x, conj (g x) * g (x - u)) * φ u`.
* `Complex.IsPositiveDefinite.fourier_gaussian_mul_nonneg`: for `a > 0`, the Fourier transform
  of `u ↦ exp (-a u²) φ u` is real and nonnegative.
* `Real.integrable_fourier_of_nonneg`: if `f` is integrable and continuous at `0` and `𝓕 f` is
  real and nonnegative, then `𝓕 f` is integrable.
* `Complex.IsPositiveDefinite.exists_measure_charFun_gaussian`: for `b > 0`, a finite measure
  with characteristic function `exp (-b t²) φ t`.

## Proof

1. Integral positivity on intervals (`IsPositiveDefinite.intervalIntegral_nonneg`) passes to
   `ℝ` by dominated convergence. The substitution `y = x - u` and Fubini turn the double
   integral into the pairing of `φ` with the autocorrelation of `g`.
2. For a Gaussian `g` modulated by a character, the autocorrelation is a Gaussian times the
   character (`integral_cexp_quadratic`). So the pairing is a positive multiple of the Fourier
   transform of `φ` damped by a Gaussian, which is therefore nonnegative.
3. Gaussian duality at the origin (as in Mathlib's proof of Fourier inversion, but with no
   integrability assumption on `𝓕 f`) plus monotone convergence shows that a nonnegative
   Fourier transform is integrable. Fourier inversion then exhibits the damped function as the
   characteristic function of the measure with that density.
4. Letting the damping go to zero: Lévy's continuity theorem gives tightness
   (`isTightMeasureSet_of_tendsto_charFun`), Prokhorov compactness and the pseudo-metrisability
   of `ProbabilityMeasure ℝ` give a convergent subsequence, and the limit has characteristic
   function `φ / φ 0`. Uniqueness is `Measure.ext_of_charFun`.
-/

open MeasureTheory Filter Set
open scoped ComplexOrder ComplexConjugate Topology FourierTransform Real

namespace Complex

namespace IsPositiveDefinite

variable {φ : ℝ → ℂ}

/-- Integrability of `y ↦ conj (g x) * g y * φ (x - y)`. -/
theorem integrable_kernel_right (hφ : IsPositiveDefinite φ) (hφc : Continuous φ) {g : ℝ → ℂ}
    (hgi : Integrable g) (x : ℝ) :
    Integrable (fun y => conj (g x) * g y * φ (x - y)) := by
  have h : Integrable (fun y => (conj (g x) * φ (x - y)) * g y) :=
    hgi.bdd_mul (c := ‖g x‖ * (φ 0).re) (by fun_prop)
      (ae_of_all _ fun y => by
        rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul_of_nonneg_left (hφ.norm_le _) (norm_nonneg _))
  exact h.congr (ae_of_all _ fun y => by ring)

/-- **Integral positivity on `ℝ` for integrable `g`.** -/
theorem integral_integral_nonneg (hφ : IsPositiveDefinite φ) (hφc : Continuous φ) {g : ℝ → ℂ}
    (hg : Continuous g) (hgi : Integrable g) :
    0 ≤ ∫ x, ∫ y, conj (g x) * g y * φ (x - y) := by
  set F : ℝ → ℝ → ℂ := fun x y => conj (g x) * g y * φ (x - y) with hF
  have hFc : Continuous (Function.uncurry F) := by
    simp only [hF]; fun_prop
  have hFy := hφ.integrable_kernel_right hφc hgi
  set B : ℝ := (φ 0).re
  set G : ℝ := ∫ y, ‖g y‖
  -- truncated inner integrals
  set J : ℕ → ℝ → ℂ := fun n x => ∫ y in (-(n : ℝ))..n, F x y with hJ
  have hJc : ∀ n, Continuous (J n) := fun n =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hFc continuous_const
  have hnorm : ∀ x y, ‖F x y‖ ≤ ‖g x‖ * B * ‖g y‖ := by
    intro x y
    simp only [hF, norm_mul, RCLike.norm_conj]
    have := hφ.norm_le (x - y)
    have h1 := norm_nonneg (g x); have h2 := norm_nonneg (g y)
    nlinarith [mul_nonneg h1 h2]
  have hJbound : ∀ n x, ‖J n x‖ ≤ ‖g x‖ * B * G := by
    intro n x
    have hle : (-(n : ℝ)) ≤ n := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    simp only [hJ]
    rw [intervalIntegral.integral_of_le hle]
    calc ‖∫ y in Ioc (-(n : ℝ)) n, F x y‖ ≤ ∫ y in Ioc (-(n : ℝ)) n, ‖F x y‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ y, ‖F x y‖ :=
          setIntegral_le_integral (hFy x).norm (ae_of_all _ fun y => norm_nonneg _)
      _ ≤ ∫ y, ‖g x‖ * B * ‖g y‖ :=
          integral_mono (hFy x).norm (hgi.norm.const_mul _) (fun y => hnorm x y)
      _ = ‖g x‖ * B * G := by rw [integral_const_mul]
  -- the truncated double integrals are nonnegative
  have hI : ∀ n : ℕ, 0 ≤ ∫ x, (Ioc (-(n : ℝ)) n).indicator (J n) x := by
    intro n
    have hle : (-(n : ℝ)) ≤ n := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hle]
    exact hφ.intervalIntegral_nonneg hφc hg hle
  -- dominated convergence
  have hlim : Tendsto (fun n : ℕ => ∫ x, (Ioc (-(n : ℝ)) n).indicator (J n) x) atTop
      (𝓝 (∫ x, ∫ y, F x y)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g x‖ * B * G)
      (fun n => ((hJc n).aestronglyMeasurable).indicator measurableSet_Ioc)
      ((hgi.norm.mul_const B).mul_const G) (fun n => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => ?_)
    · by_cases hx : x ∈ Ioc (-(n : ℝ)) n
      · rw [indicator_of_mem hx]; exact hJbound n x
      · rw [indicator_of_notMem hx, norm_zero]
        have := norm_nonneg (g x)
        have hB : 0 ≤ B := hφ.re_zero_nonneg
        have hG : 0 ≤ G := MeasureTheory.integral_nonneg fun y => norm_nonneg _
        positivity
    · have hT : Tendsto (fun n : ℕ => J n x) atTop (𝓝 (∫ y, F x y)) :=
        intervalIntegral_tendsto_integral (hFy x)
          (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop
      refine hT.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_gt |x|
      filter_upwards [eventually_ge_atTop N] with n hn
      have hn' : |x| < n := lt_of_lt_of_le hN (by exact_mod_cast hn)
      rw [indicator_of_mem]
      exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  exact ge_of_tendsto' hlim hI

/-- The kernel `(x, u) ↦ conj (g x) * g (x - u) * φ u` is integrable on `ℝ × ℝ`. -/
theorem integrable_autocorr_kernel (hφ : IsPositiveDefinite φ) (hφc : Continuous φ) {g : ℝ → ℂ}
    (hg : Continuous g) (hgi : Integrable g) :
    Integrable (Function.uncurry fun x u => conj (g x) * g (x - u) * φ u)
      (volume.prod volume) := by
  set K : ℝ → ℝ → ℂ := fun x u => conj (g x) * g (x - u) * φ u with hK
  have hKc : Continuous (Function.uncurry K) := by
    simp only [hK]; fun_prop
  set B : ℝ := (φ 0).re
  set G : ℝ := ∫ y, ‖g y‖
  rw [integrable_prod_iff hKc.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun x => ?_, ?_⟩
  · have h : Integrable (fun u => φ u * (conj (g x) * g (x - u))) :=
      ((hgi.comp_sub_left x).const_mul (conj (g x))).bdd_mul (c := B) (by fun_prop)
        (ae_of_all _ fun u => hφ.norm_le u)
    exact h.congr (ae_of_all _ fun u => by simp only [Function.uncurry, hK]; ring)
  · refine Integrable.mono' ((hgi.norm.mul_const B).mul_const G)
      (hKc.aestronglyMeasurable.norm.integral_prod_right') (ae_of_all _ fun x => ?_)
    have hint : Integrable (fun u => ‖g x‖ * B * ‖g (x - u)‖) :=
      (hgi.comp_sub_left x).norm.const_mul _
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun u => norm_nonneg _)]
    calc ∫ u, ‖Function.uncurry K (x, u)‖ ≤ ∫ u, ‖g x‖ * B * ‖g (x - u)‖ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun u => norm_nonneg _) hint
            (ae_of_all _ fun u => ?_)
          simp only [Function.uncurry, hK, norm_mul, RCLike.norm_conj]
          have := hφ.norm_le u
          have h1 := norm_nonneg (g x); have h2 := norm_nonneg (g (x - u))
          nlinarith [mul_nonneg h1 h2]
      _ = ‖g x‖ * B * G := by
          rw [integral_const_mul, integral_sub_left_eq_self (fun y => ‖g y‖)]

/-- **Pairing with an autocorrelation.** For continuous positive-definite `φ` and continuous
integrable `g`, `0 ≤ ∫ u, (∫ x, conj (g x) * g (x - u)) * φ u`. -/
theorem integral_autocorr_mul_nonneg (hφ : IsPositiveDefinite φ) (hφc : Continuous φ)
    {g : ℝ → ℂ} (hg : Continuous g) (hgi : Integrable g) :
    0 ≤ ∫ u, (∫ x, conj (g x) * g (x - u)) * φ u := by
  have h0 := hφ.integral_integral_nonneg hφc hg hgi
  have h1 : (∫ x, ∫ y, conj (g x) * g y * φ (x - y)) =
      ∫ x, ∫ u, conj (g x) * g (x - u) * φ u := by
    congr 1
    funext x
    rw [← integral_sub_left_eq_self (fun y => conj (g x) * g y * φ (x - y)) volume x]
    simp only [sub_sub_cancel]
  have h2 := integral_integral_swap (hφ.integrable_autocorr_kernel hφc hg hgi)
  have h3 : (∫ u, ∫ x, conj (g x) * g (x - u) * φ u) =
      ∫ u, (∫ x, conj (g x) * g (x - u)) * φ u := by
    congr 1
    funext u
    rw [integral_mul_const]
  rw [h1, h2, h3] at h0
  exact h0

end IsPositiveDefinite

/-- The modulated Gaussian `y ↦ exp (-2a y² + 2πiξ y)`. -/
noncomputable def gaussChar (a ξ : ℝ) (y : ℝ) : ℂ :=
  cexp (-(2 * a : ℂ) * (y : ℂ) ^ 2 + (2 * π * ξ * I) * y + 0)

theorem continuous_gaussChar (a ξ : ℝ) : Continuous (gaussChar a ξ) := by
  unfold gaussChar; fun_prop

theorem integrable_gaussChar {a : ℝ} (ha : 0 < a) (ξ : ℝ) : Integrable (gaussChar a ξ) :=
  integrable_cexp_quadratic (b := 2 * a) (by simpa using ha) _ _

/-- The autocorrelation of the modulated Gaussian:
`∫ x, conj (g x) * g (x - u) = (π / (4a))^(1/2) * exp (-a u² - 2πiξu)`. -/
theorem integral_conj_gaussChar_mul {a : ℝ} (ha : 0 < a) (ξ u : ℝ) :
    ∫ x, conj (gaussChar a ξ x) * gaussChar a ξ (x - u) =
      ((π : ℂ) / (4 * a)) ^ (1 / 2 : ℂ) * cexp (-(a : ℂ) * u ^ 2 - 2 * π * ξ * I * u) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hpt : ∀ x : ℝ, conj (gaussChar a ξ x) * gaussChar a ξ (x - u) =
      cexp (-(4 * a : ℂ) * (x : ℂ) ^ 2 + (4 * a * u : ℂ) * x
        + (-(2 * a : ℂ) * u ^ 2 - 2 * π * ξ * I * u)) := by
    intro x
    simp only [gaussChar, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_add, map_mul, map_neg, map_pow, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I, map_zero]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_cexp_quadratic (b := -(4 * a : ℂ)) (by simpa using ha)]
  congr 1
  · congr 1
    ring
  · congr 1
    field_simp
    ring

namespace IsPositiveDefinite

variable {φ : ℝ → ℂ}

/-- **The Gaussian-damped Fourier transform of a positive-definite function is nonnegative.**
For continuous positive-definite `φ`, `a > 0` and every `ξ`,
`0 ≤ 𝓕 (fun u => exp (-a u²) * φ u) ξ` (real and nonnegative). -/
theorem fourier_gaussian_mul_nonneg (hφ : IsPositiveDefinite φ) (hφc : Continuous φ)
    {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    0 ≤ 𝓕 (fun u : ℝ => cexp (-(a : ℂ) * u ^ 2) * φ u) ξ := by
  have h := hφ.integral_autocorr_mul_nonneg hφc (continuous_gaussChar a ξ)
    (integrable_gaussChar ha ξ)
  simp_rw [integral_conj_gaussChar_mul ha ξ, mul_assoc] at h
  rw [integral_const_mul] at h
  set s : ℂ := ((π : ℂ) / (4 * a)) ^ (1 / 2 : ℂ) with hs
  have hsr : s = ((Real.pi / (4 * a)) ^ (1 / 2 : ℝ) : ℝ) := by
    rw [hs, Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  have hspos : (0 : ℝ) < (Real.pi / (4 * a)) ^ (1 / 2 : ℝ) := by positivity
  have hF : 𝓕 (fun u : ℝ => cexp (-(a : ℂ) * u ^ 2) * φ u) ξ =
      ∫ u : ℝ, cexp (-(a : ℂ) * u ^ 2 - 2 * π * ξ * I * u) * φ u := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1
    funext u
    rw [smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hF]
  have hinv : (0 : ℂ) ≤ s⁻¹ := by
    rw [hsr, ← Complex.ofReal_inv]
    exact Complex.zero_le_real.mpr (inv_nonneg.mpr hspos.le)
  have hs0 : s ≠ 0 := by
    rw [hsr]; exact_mod_cast hspos.ne'
  have := mul_nonneg hinv h
  rw [← mul_assoc, inv_mul_cancel₀ hs0, one_mul] at this
  simp only [mul_assoc] at this ⊢
  exact this

end IsPositiveDefinite

end Complex

namespace Real

open Complex
open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false in
/-- Gaussian duality at the origin: for integrable `f` continuous at `0`,
`∫ w, exp (-‖w‖² / c) • 𝓕 f w → f 0` as `c → ∞`. No integrability of `𝓕 f` is assumed. -/
theorem tendsto_integral_cexp_sq_smul_fourier {f : ℝ → ℂ} (hf : Integrable f)
    (h0 : ContinuousAt f 0) :
    Tendsto (fun c : ℝ => ∫ w : ℝ, cexp (-c⁻¹ * ‖w‖ ^ 2) • 𝓕 f w) atTop (𝓝 (f 0)) := by
  have B := Real.tendsto_integral_gaussian_smul' hf h0
  apply B.congr'
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  have J : Integrable (fun w : ℝ ↦ cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * π * I * ⟪(0 : ℝ), w⟫)) :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa) _ _
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner J hf
  have hG : ∀ w : ℝ, VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
      (fun w : ℝ ↦ cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * π * I * ⟪(0 : ℝ), w⟫)) w =
      (π * c : ℂ) ^ (Module.finrank ℝ ℝ / 2 : ℂ) * cexp (-π ^ 2 * c * ‖(0 : ℝ) - w‖ ^ 2) := by
    intro w
    have := fourier_gaussian_innerProductSpace' (b := (c⁻¹ : ℂ)) (by simpa using hc) (0 : ℝ) w
    have e : VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
        (fun w : ℝ ↦ cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * π * I * ⟪(0 : ℝ), w⟫)) w =
        FourierTransform.fourier
          (fun v : ℝ => cexp (-(c : ℂ)⁻¹ * ‖v‖ ^ 2 + 2 * π * I * ⟪(0 : ℝ), v⟫)) w := by
      push_cast; rfl
    rw [e, this]
    congr 1
    · congr 1; field_simp
    · congr 1; field_simp
  simp_rw [hG] at key
  rw [key]
  congr 1
  funext w
  simp
  rfl

/-- `𝓕 f` is continuous for integrable `f`. -/
theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

/-- `‖𝓕 f w‖ ≤ ∫ ‖f‖`. -/
theorem norm_fourier_le {f : ℝ → ℂ} (w : ℝ) : ‖𝓕 f w‖ ≤ ∫ v, ‖f v‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) f w

/-- **A nonnegative Fourier transform is integrable.** If `f` is integrable and continuous at
`0`, and `𝓕 f` is real and nonnegative everywhere, then `𝓕 f` is integrable. -/
theorem integrable_fourier_of_nonneg {f : ℝ → ℂ} (hf : Integrable f) (h0 : ContinuousAt f 0)
    (hpos : ∀ ξ, 0 ≤ 𝓕 f ξ) : Integrable (𝓕 f) := by
  set q : ℝ → ℝ := fun ξ => (𝓕 f ξ).re with hq_def
  have hq : ∀ ξ, 𝓕 f ξ = (q ξ : ℂ) := fun ξ =>
    Complex.ext (by simp [q]) (by simp [q, ((Complex.nonneg_iff.mp (hpos ξ)).2).symm])
  have hq0 : ∀ ξ, 0 ≤ q ξ := fun ξ => (Complex.nonneg_iff.mp (hpos ξ)).1
  have hqc : Continuous q := Complex.continuous_re.comp (continuous_fourier_of_integrable hf)
  set M : ℝ := ∫ v, ‖f v‖
  have hqM : ∀ ξ, ‖q ξ‖ ≤ M := fun ξ => by
    rw [Real.norm_of_nonneg (hq0 ξ)]
    calc q ξ ≤ ‖𝓕 f ξ‖ := by rw [hq ξ, Complex.norm_real, Real.norm_of_nonneg (hq0 ξ)]
      _ ≤ M := norm_fourier_le ξ
  -- the damped sequence
  set g : ℕ → ℝ → ℝ := fun n ξ => q ξ * Real.exp (-((n : ℝ) + 1)⁻¹ * ξ ^ 2) with hg_def
  have hgi : ∀ n, Integrable (g n) := fun n =>
    (integrable_exp_neg_mul_sq (b := ((n : ℝ) + 1)⁻¹) (by positivity)).bdd_mul
      hqc.aestronglyMeasurable (ae_of_all _ hqM)
  have hg0 : ∀ n ξ, 0 ≤ g n ξ := fun n ξ => mul_nonneg (hq0 ξ) (Real.exp_pos _).le
  -- the real limit of the damped integrals
  have hT := (tendsto_integral_cexp_sq_smul_fourier hf h0).comp
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have hTre : Tendsto (fun n : ℕ => ∫ ξ, g n ξ) atTop (𝓝 (f 0).re) := by
    have := (Complex.continuous_re.tendsto _).comp hT
    refine this.congr (fun n => ?_)
    simp only [Function.comp_apply]
    have e : (fun w : ℝ => cexp (-((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * ‖w‖ ^ 2) • 𝓕 f w) =
        fun w => ((g n w : ℝ) : ℂ) := by
      funext w
      have hw : ‖w‖ ^ 2 = w ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
      rw [hq w, smul_eq_mul, hg_def, ← Complex.ofReal_pow, hw]
      simp only [Complex.ofReal_mul, Complex.ofReal_exp]
      push_cast
      ring
    rw [e, integral_complex_ofReal, Complex.ofReal_re]
  -- monotone convergence in the lower integral
  have hlin : Tendsto (fun n : ℕ => ∫⁻ ξ, ENNReal.ofReal (g n ξ)) atTop
      (𝓝 (∫⁻ ξ, ENNReal.ofReal (q ξ))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (hgi n).aemeasurable.ennreal_ofReal)
      (ae_of_all _ fun ξ => ?_) (ae_of_all _ fun ξ => ?_)
    · intro m n hmn
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (hq0 ξ))
      refine Real.exp_le_exp.mpr ?_
      have hm : ((m : ℝ) + 1)⁻¹ ≥ ((n : ℝ) + 1)⁻¹ := by
        have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        gcongr
      nlinarith [sq_nonneg ξ]
    · refine ENNReal.tendsto_ofReal ?_
      have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
      have : Tendsto (fun n : ℕ => q ξ * Real.exp (-((n : ℝ) + 1)⁻¹ * ξ ^ 2)) atTop
          (𝓝 (q ξ * Real.exp (-0 * ξ ^ 2))) :=
        tendsto_const_nhds.mul ((Real.continuous_exp.tendsto _).comp
          ((hinv.neg).mul_const _))
      simpa [hg_def] using this
  have hlin' : Tendsto (fun n : ℕ => ∫⁻ ξ, ENNReal.ofReal (g n ξ)) atTop
      (𝓝 (ENNReal.ofReal (f 0).re)) := by
    refine (ENNReal.tendsto_ofReal hTre).congr (fun n => ?_)
    exact ofReal_integral_eq_lintegral_ofReal (hgi n) (ae_of_all _ (hg0 n))
  have hfin : ∫⁻ ξ, ENNReal.ofReal (q ξ) < ⊤ := by
    rw [tendsto_nhds_unique hlin hlin']
    exact ENNReal.ofReal_lt_top
  have hqi : Integrable q :=
    ⟨hqc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hq0)).mpr hfin⟩
  exact hqi.ofReal.congr (ae_of_all _ fun ξ => (hq ξ).symm)

end Real

namespace Complex

namespace IsPositiveDefinite

variable {φ : ℝ → ℂ}

/-- `charFun (c • μ) t = c.toReal * charFun μ t`. -/
theorem charFun_smul_measure (μ : Measure ℝ) (c : ENNReal) (t : ℝ) :
    charFun (c • μ) t = (c.toReal : ℂ) * charFun μ t := by
  rw [charFun_apply_real, charFun_apply_real, integral_smul_measure, Complex.real_smul]

/-- **Gaussian-damped Bochner.** For continuous positive-definite `φ` and `a > 0` there is a
finite measure whose characteristic function is `t ↦ exp (-a (t/2π)²) φ (t/2π)`. -/
theorem exists_measure_charFun_damped (hφ : IsPositiveDefinite φ) (hφc : Continuous φ)
    {a : ℝ} (ha : 0 < a) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ ∀ t : ℝ,
      charFun μ t = cexp (-(a : ℂ) * ((t / (2 * π) : ℝ) : ℂ) ^ 2) * φ (t / (2 * π)) := by
  set ψ : ℝ → ℂ := fun u => cexp (-(a : ℂ) * (u : ℂ) ^ 2) * φ u with hψ
  have hψc : Continuous ψ := by simp only [hψ]; fun_prop
  have hψi : Integrable ψ := by
    refine ((integrable_exp_neg_mul_sq ha).const_mul (φ 0).re).mono' hψc.aestronglyMeasurable
      (ae_of_all _ fun u => ?_)
    simp only [hψ, norm_mul, Complex.norm_exp]
    have h1 : (-(a : ℂ) * (u : ℂ) ^ 2).re = -a * u ^ 2 := by
      simp [← Complex.ofReal_pow]
    rw [h1, mul_comm]
    exact mul_le_mul_of_nonneg_right (hφ.norm_le u) (Real.exp_pos _).le
  have hpos : ∀ ξ, 0 ≤ 𝓕 ψ ξ := fun ξ => hφ.fourier_gaussian_mul_nonneg hφc ha ξ
  have hpi : Integrable (𝓕 ψ) := Real.integrable_fourier_of_nonneg hψi hψc.continuousAt hpos
  have hinv : 𝓕⁻ (𝓕 ψ) = ψ := hψc.fourierInv_fourier_eq hψi hpi
  set q : ℝ → ℝ := fun ξ => (𝓕 ψ ξ).re with hq_def
  have hq : ∀ ξ, 𝓕 ψ ξ = (q ξ : ℂ) := fun ξ =>
    Complex.ext (by simp [q]) (by simp [q, ((Complex.nonneg_iff.mp (hpos ξ)).2).symm])
  have hq0 : ∀ ξ, 0 ≤ q ξ := fun ξ => (Complex.nonneg_iff.mp (hpos ξ)).1
  have hqc : Continuous q :=
    Complex.continuous_re.comp (Real.continuous_fourier_of_integrable hψi)
  have hqi : Integrable q := by
    refine hpi.norm.mono' hqc.aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
    rw [hq ξ, Complex.norm_real]
  refine ⟨volume.withDensity (fun ξ => ENNReal.ofReal (q ξ)),
    isFiniteMeasure_withDensity_ofReal hqi.2, fun t => ?_⟩
  rw [charFun_apply_real, integral_withDensity_eq_integral_toReal_smul
    (f := fun ξ => ENNReal.ofReal (q ξ)) hqc.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hval : ψ (t / (2 * π)) = 𝓕⁻ (𝓕 ψ) (t / (2 * π)) := by rw [hinv]
  rw [show cexp (-(a : ℂ) * ((t / (2 * π) : ℝ) : ℂ) ^ 2) * φ (t / (2 * π)) = ψ (t / (2 * π))
    from rfl, hval, Real.fourierInv_eq']
  congr 1
  funext ξ
  rw [ENNReal.toReal_ofReal (hq0 ξ), hq ξ, Complex.real_smul, smul_eq_mul, mul_comm]
  congr 2
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  field_simp

/-- For continuous positive-definite `φ` and `b > 0` there is a finite measure whose
characteristic function is `t ↦ exp (-b t²) φ t`. -/
theorem exists_measure_charFun_gaussian (hφ : IsPositiveDefinite φ) (hφc : Continuous φ)
    {b : ℝ} (hb : 0 < b) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ ∀ t : ℝ,
      charFun μ t = cexp (-(b : ℂ) * (t : ℂ) ^ 2) * φ t := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  obtain ⟨μ, hμ, hchar⟩ := (hφ.comp_mul (2 * π)).exists_measure_charFun_damped
    (by fun_prop) (a := b * (2 * π) ^ 2) (by positivity)
  refine ⟨μ, hμ, fun t => ?_⟩
  rw [hchar t]
  have e : 2 * π * (t / (2 * π)) = t := by field_simp
  rw [e]
  congr 2
  push_cast
  field_simp

/-- **Bochner's theorem.** A continuous positive-definite function `φ : ℝ → ℂ` is the
characteristic function of a finite measure on `ℝ`. -/
theorem exists_measure_charFun_eq (hφ : IsPositiveDefinite φ) (hφc : Continuous φ) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ ∀ t : ℝ, charFun μ t = φ t := by
  by_cases h0 : (φ 0).re = 0
  · refine ⟨0, inferInstance, fun t => ?_⟩
    have h := hφ.norm_le t
    rw [h0] at h
    rw [charFun_zero_measure, norm_le_zero_iff.mp h]
  set r : ℝ := (φ 0).re with hr
  have hr0 : 0 < r := lt_of_le_of_ne hφ.re_zero_nonneg (Ne.symm h0)
  have hφ0 : φ 0 = (r : ℂ) := Complex.ext (by simp [r]) (by simp [hφ.im_zero])
  choose μ hμf hμ using fun n : ℕ =>
    hφ.exists_measure_charFun_gaussian hφc (b := ((n : ℝ) + 1)⁻¹) (by positivity)
  set ν : ℕ → Measure ℝ := fun n => ENNReal.ofReal r⁻¹ • μ n with hν
  have hνf : ∀ n, IsFiniteMeasure (ν n) := fun n =>
    ⟨by
      simp only [hν, Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  have hνchar : ∀ n t, charFun (ν n) t =
      ((r⁻¹ : ℝ) : ℂ) * (cexp (-(((n : ℝ) + 1)⁻¹ : ℝ) * (t : ℂ) ^ 2) * φ t) := by
    intro n t
    rw [charFun_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hr0.le), hμ n t]
  have hνprob : ∀ n, IsProbabilityMeasure (ν n) := by
    intro n
    have h := charFun_zero (μ := ν n)
    rw [hνchar n 0, hφ0] at h
    simp only [Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, Complex.exp_zero, one_mul] at h
    have h' : (ν n).real univ = 1 := by
      have : ((r⁻¹ : ℝ) : ℂ) * (r : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ hr0.ne', Complex.ofReal_one]
      rw [this] at h
      exact_mod_cast h.symm
    constructor
    rw [measureReal_def, ENNReal.toReal_eq_one_iff] at h'
    exact h'
  -- the limit of the characteristic functions
  set F : ℝ → ℂ := fun t => ((r⁻¹ : ℝ) : ℂ) * φ t with hF
  have hFc : ContinuousAt F 0 := by simp only [hF]; fun_prop
  have hconv : ∀ t, Tendsto (fun n => charFun (ν n) t) atTop (𝓝 (F t)) := by
    intro t
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    have hexp : Tendsto (fun n : ℕ => cexp (-(((n : ℝ) + 1)⁻¹ : ℝ) * (t : ℂ) ^ 2)) atTop
        (𝓝 (cexp (-((0 : ℝ) : ℂ) * (t : ℂ) ^ 2))) :=
      (Complex.continuous_exp.tendsto _).comp
        (((Complex.continuous_ofReal.tendsto _).comp hinv).neg.mul_const _)
    have := (tendsto_const_nhds (x := ((r⁻¹ : ℝ) : ℂ))).mul (hexp.mul_const (φ t))
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul] at this
    refine this.congr (fun n => ?_)
    rw [hνchar n t]
  have htight : IsTightMeasureSet (range ν) :=
    isTightMeasureSet_of_tendsto_charFun (μ := ν) hFc hconv
  -- Prokhorov
  let P : ℕ → ProbabilityMeasure ℝ := fun n => ⟨ν n, hνprob n⟩
  have hcomp : IsCompact (closure (range P)) := by
    refine isCompact_closure_of_isTightMeasureSet (S := range P) ?_
    convert htight using 1
    ext m
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨P n, ⟨n, rfl⟩, rfl⟩
  obtain ⟨Q, -, σ, hσ, hlim⟩ :=
    hcomp.tendsto_subseq (x := P) (fun n => subset_closure (mem_range_self n))
  have hQ : ∀ t, charFun (Q : Measure ℝ) t = F t := by
    intro t
    have h1 := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hlim) t
    have h2 := (hconv t).comp hσ.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  refine ⟨ENNReal.ofReal r • (Q : Measure ℝ),
    ⟨by
      simp only [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩, fun t => ?_⟩
  rw [charFun_smul_measure, ENNReal.toReal_ofReal hr0.le, hQ t, hF]
  simp only
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hr0.ne', Complex.ofReal_one, one_mul]

/-- **Bochner's theorem, with uniqueness.** The representing finite measure is unique. -/
theorem existsUnique_measure_charFun_eq (hφ : IsPositiveDefinite φ) (hφc : Continuous φ) :
    ∃! μ : Measure ℝ, IsFiniteMeasure μ ∧ ∀ t : ℝ, charFun μ t = φ t := by
  obtain ⟨μ, hμ, h⟩ := hφ.exists_measure_charFun_eq hφc
  refine ⟨μ, ⟨hμ, h⟩, fun ν hν => ?_⟩
  obtain ⟨hνf, hν'⟩ := hν
  exact Measure.ext_of_charFun (funext fun t => (hν' t).trans (h t).symm)

end IsPositiveDefinite

end Complex
