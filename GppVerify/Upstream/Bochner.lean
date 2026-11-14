/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import GppVerify.Upstream.PositiveDefiniteFunction
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Bochner's theorem on `ℝ`

A continuous positive-definite function `φ : ℝ → ℂ` is the characteristic function of a finite
measure on `ℝ`.

## Main results

* `IsPositiveDefinite.integral_autocorr_mul_nonneg`: for continuous positive-definite `φ` and
  continuous integrable `g`, `0 ≤ ∫ u, (∫ x, conj (g x) * g (x - u)) * φ u`.
* `IsPositiveDefinite.fourier_gaussian_mul_nonneg`: for `a > 0`, the Fourier transform of
  `u ↦ exp (-a u²) φ u` is real and nonnegative at every point.

## Proof

Integral positivity on intervals (`IsPositiveDefinite.intervalIntegral_nonneg`) passes to `ℝ` by
dominated convergence. The substitution `y = x - u` and Fubini turn the double integral into the
pairing of `φ` with the autocorrelation of `g`. For a Gaussian `g` modulated by a character, the
autocorrelation is a Gaussian times the character (`integral_cexp_quadratic`). So the pairing is a
positive multiple of the Fourier transform of `φ` damped by a Gaussian.
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

end Complex
