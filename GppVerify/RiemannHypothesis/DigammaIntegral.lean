/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import GppVerify.RiemannHypothesis.DigammaGaussSeries

/-!
# Explicit formula, stage E6 (Archimedean term), part 1: Gauss's integral for the digamma function

For `Re z > 0`,

  `ψ(z) = -γ + ∫₀^∞ (e^{-t} - e^{-z t}) / (1 - e^{-t}) dt`.

It is obtained from the Gauss series of stage E2a by writing each `1/(n+1) - 1/(n+1+z)` as
`∫₀^∞ e^{-(n+1)t} (1 - e^{-z t}) dt` and summing under the integral, which is legitimate because
`‖1 - e^{-z t}‖ ≤ ‖z‖ t` makes `∑ₙ ∫ ‖…‖ ≤ ‖z‖ ∑ₙ (n+1)⁻²` finite.
-/

open Complex Set MeasureTheory

namespace GppDigammaIntegral

/-- `‖1 - e^{-w}‖ ≤ ‖w‖` for `Re w ≥ 0`. -/
theorem norm_one_sub_exp_neg_le {w : ℂ} (hw : 0 ≤ w.re) : ‖1 - Complex.exp (-w)‖ ≤ ‖w‖ := by
  have hd : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun u : ℝ => Complex.exp (-(u : ℂ) * w))
      (-w * Complex.exp (-(x : ℂ) * w)) (Icc (0 : ℝ) 1) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => (-(u : ℂ) * w)) (-w) x := by
      have := ((hasDerivAt_id x).ofReal_comp.neg).mul_const w
      simpa using this
    have := h1.cexp
    simpa [mul_comm] using this.hasDerivWithinAt
  have hb : ∀ x ∈ Ico (0 : ℝ) 1, ‖-w * Complex.exp (-(x : ℂ) * w)‖ ≤ ‖w‖ := by
    intro x hx
    rw [norm_mul, norm_neg, Complex.norm_exp]
    have : (-(x : ℂ) * w).re ≤ 0 := by
      simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      nlinarith [hx.1, hw]
    have h2 : Real.exp (-(x : ℂ) * w).re ≤ 1 := Real.exp_le_one_iff.2 this
    calc ‖w‖ * Real.exp (-(x : ℂ) * w).re ≤ ‖w‖ * 1 := by gcongr
      _ = ‖w‖ := mul_one _
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb
  simpa [norm_sub_rev] using this

/-- The `n`-th summand of the Gauss series as an integrand. -/
noncomputable def F (z : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-((n : ℂ) + 1) * t) * (1 - Complex.exp (-z * t))

theorem F_eq (z : ℂ) (n : ℕ) (t : ℝ) :
    F z n t = Complex.exp (-((n : ℂ) + 1) * t) - Complex.exp (-((n : ℂ) + 1 + z) * t) := by
  unfold F
  rw [mul_sub, mul_one, ← Complex.exp_add]
  congr 2
  ring

theorem norm_F_le {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖F z n t‖ ≤ ‖z‖ * (t * Real.exp (-((n : ℝ) + 1) * t)) := by
  unfold F
  rw [norm_mul]
  have h1 : ‖Complex.exp (-((n : ℂ) + 1) * t)‖ = Real.exp (-((n : ℝ) + 1) * t) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h2 : ‖1 - Complex.exp (-z * t)‖ ≤ ‖z‖ * t := by
    have := norm_one_sub_exp_neg_le (w := z * t) (by simpa using mul_nonneg hz ht)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht] at this
    simpa [neg_mul] using this
  rw [h1]
  calc Real.exp (-((n : ℝ) + 1) * t) * ‖1 - Complex.exp (-z * t)‖
      ≤ Real.exp (-((n : ℝ) + 1) * t) * (‖z‖ * t) := by gcongr
    _ = ‖z‖ * (t * Real.exp (-((n : ℝ) + 1) * t)) := by ring

theorem integrableOn_exp_neg {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-a * t)) (Ioi 0) := by
  have := integrableOn_exp_mul_complex_Ioi (a := -a) (by simpa using ha) 0
  simpa using this

theorem integral_exp_neg {a : ℂ} (ha : 0 < a.re) :
    ∫ t : ℝ in Ioi 0, Complex.exp (-a * t) = a⁻¹ := by
  have := integral_exp_mul_complex_Ioi (a := -a) (by simpa using ha) 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at this
  rw [this]
  have : a ≠ 0 := fun h => by simp [h] at ha
  field_simp

theorem integrableOn_F {z : ℂ} (hz : 0 < z.re) (n : ℕ) : IntegrableOn (F z n) (Ioi 0) := by
  have h1 : 0 < ((n : ℂ) + 1).re := by simp; positivity
  have h2 : 0 < ((n : ℂ) + 1 + z).re := by simp; positivity
  have := (integrableOn_exp_neg h1).sub (integrableOn_exp_neg h2)
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [F_eq, Pi.sub_apply]

theorem integral_F {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ t : ℝ in Ioi 0, F z n t = GppDigammaSeries.digammaSeriesTerm z n := by
  have h1 : 0 < ((n : ℂ) + 1).re := by simp; positivity
  have h2 : 0 < ((n : ℂ) + 1 + z).re := by simp; positivity
  have e : ∀ t : ℝ, F z n t = Complex.exp (-((n : ℂ) + 1) * t) - Complex.exp (-((n : ℂ) + 1 + z) * t) :=
    fun t => F_eq z n t
  simp_rw [e]
  rw [integral_sub (integrableOn_exp_neg h1) (integrableOn_exp_neg h2), integral_exp_neg h1,
    integral_exp_neg h2]
  rfl

theorem integrableOn_t_exp {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-a * t)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := a) (by norm_num)
    (by norm_num) ha
  simpa using this

theorem integral_t_exp {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ in Ioi 0, t * Real.exp (-a * t) = 1 / a ^ 2 := by
  have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := a) (by norm_num) ha
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.Gamma_two, mul_one] at this
  have e : ∀ t : ℝ, t * Real.exp (-a * t) = t * Real.exp (-(a * t)) := fun t => by ring_nf
  simp_rw [e]
  rw [this]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div_pow]

theorem summable_integral_norm_F {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0, ‖F z n t‖) := by
  have hbound : ∀ n : ℕ, ∫ t : ℝ in Ioi 0, ‖F z n t‖ ≤ ‖z‖ * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hI := (integrableOn_t_exp hn).const_mul ‖z‖
    have hle : ∫ t : ℝ in Ioi 0, ‖F z n t‖ ≤ ∫ t : ℝ in Ioi 0, ‖z‖ * (t * Real.exp (-((n : ℝ) + 1) * t)) := by
      refine setIntegral_mono_on (integrableOn_F hz n).norm hI measurableSet_Ioi (fun t ht => ?_)
      exact norm_F_le hz.le n (le_of_lt ht)
    rw [integral_const_mul, integral_t_exp hn] at hle
    exact hle
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _)) hbound ?_
  refine Summable.mul_left _ ?_
  have : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    simpa using (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
  exact this

/-- `1 - e^{-t}` is positive for `t > 0`. -/
theorem one_sub_exp_neg_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  have := Real.exp_lt_exp.2 (by linarith : -t < 0)
  rw [Real.exp_zero] at this
  linarith

/-- The closed form of the summand series, for `t > 0`. -/
noncomputable def G (z : ℂ) (t : ℝ) : ℂ :=
  (1 - Complex.exp (-z * t)) * (Complex.exp (-(t : ℂ)) / (1 - Complex.exp (-(t : ℂ))))

theorem tsum_F_eq {z : ℂ} {t : ℝ} (ht : 0 < t) : ∑' n : ℕ, F z n t = G z t := by
  have hr : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
    rw [Complex.norm_exp]
    have := Real.exp_lt_exp.2 (by linarith : -t < 0)
    simpa using this
  have hgeo := hasSum_geometric_of_norm_lt_one hr
  have hF : ∀ n : ℕ, F z n t = (Complex.exp (-(t : ℂ)) * Complex.exp (-(t : ℂ)) ^ n) *
      (1 - Complex.exp (-z * t)) := by
    intro n
    have e : Complex.exp (-((n : ℂ) + 1) * t) =
        Complex.exp (-(t : ℂ)) * Complex.exp (-(t : ℂ)) ^ n := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      ring
    unfold F
    rw [e]
  simp_rw [hF]
  rw [tsum_mul_right, tsum_mul_left, hgeo.tsum_eq, G]
  have : (1 - Complex.exp (-(t : ℂ))) ≠ 0 := by
    intro h
    have h1 : Complex.exp (-(t : ℂ)) = 1 := by linear_combination -h
    rw [h1] at hr
    simp at hr
  field_simp

theorem norm_G_le {z : ℂ} (hz : 0 ≤ z.re) {t : ℝ} (ht : 0 < t) :
    ‖G z t‖ ≤ ‖z‖ * Real.exp (-(1 / 2) * t) := by
  have h1 : ‖1 - Complex.exp (-z * t)‖ ≤ ‖z‖ * t := by
    have := norm_one_sub_exp_neg_le (w := z * t) (by simpa using mul_nonneg hz ht.le)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le] at this
    simpa [neg_mul] using this
  have hden := one_sub_exp_neg_pos ht
  have h2 : ‖Complex.exp (-(t : ℂ)) / (1 - Complex.exp (-(t : ℂ)))‖ =
      Real.exp (-t) / (1 - Real.exp (-t)) := by
    rw [norm_div, Complex.norm_exp]
    have : (1 : ℂ) - Complex.exp (-(t : ℂ)) = ((1 - Real.exp (-t) : ℝ) : ℂ) := by
      push_cast
      rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
    rw [this, Complex.norm_real, Real.norm_of_nonneg hden.le]
    simp
  have h3 : t * (Real.exp (-t) / (1 - Real.exp (-t))) ≤ Real.exp (-(1 / 2) * t) := by
    rw [← mul_div_assoc, div_le_iff₀ hden]
    have hs : t / 2 ≤ Real.sinh (t / 2) := Real.self_le_sinh_iff.2 (by linarith)
    rw [Real.sinh_eq] at hs
    have e1 : Real.exp (-(t / 2)) = Real.exp (-t / 2) := by ring_nf
    have hexp : Real.exp (-t) = Real.exp (-(1/2) * t) * Real.exp (-(1/2) * t) := by
      rw [← Real.exp_add]; ring_nf
    have hexp2 : Real.exp (t / 2) * Real.exp (-(1/2) * t) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    set e := Real.exp (-(1/2) * t) with he
    have hepos : 0 < e := Real.exp_pos _
    have : Real.exp (-(t / 2)) = e := by rw [he]; ring_nf
    rw [this] at hs
    have hz2 : Real.exp (t / 2) = e⁻¹ := by
      field_simp; linarith
    rw [hz2] at hs
    rw [hexp]
    have : t * (e * e) ≤ e * (1 - e * e) := by
      have h4 : t ≤ e⁻¹ - e := by linarith
      have h5 : t * e ≤ 1 - e * e := by
        have := mul_le_mul_of_nonneg_right h4 hepos.le
        rwa [sub_mul, inv_mul_cancel₀ hepos.ne'] at this
      nlinarith
    exact this
  unfold G
  rw [norm_mul, h2]
  calc ‖1 - Complex.exp (-z * t)‖ * (Real.exp (-t) / (1 - Real.exp (-t)))
      ≤ ‖z‖ * t * (Real.exp (-t) / (1 - Real.exp (-t))) := by gcongr
    _ = ‖z‖ * (t * (Real.exp (-t) / (1 - Real.exp (-t)))) := by ring
    _ ≤ ‖z‖ * Real.exp (-(1 / 2) * t) := by gcongr

theorem integrableOn_G {z : ℂ} (hz : 0 ≤ z.re) : IntegrableOn (G z) (Ioi 0) := by
  have hdom : IntegrableOn (fun t : ℝ => ‖z‖ * Real.exp (-(1 / 2) * t)) (Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ => ‖z‖ * ‖Complex.exp (-(1 / 2 : ℂ) * t)‖) (Ioi 0) :=
      (integrableOn_exp_neg (a := (1 / 2 : ℂ)) (by simp)).norm.const_mul ‖z‖
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Complex.norm_exp]
    congr 2
    simp
  refine Integrable.mono' hdom ?_ ?_
  · have : ContinuousOn (G z) (Ioi 0) := by
      unfold G
      refine ContinuousOn.mul (by fun_prop) (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
      intro t ht h
      have h1 : Complex.exp (-(t : ℂ)) = 1 := by linear_combination -h
      have hr : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
        rw [Complex.norm_exp]
        have := Real.exp_lt_exp.2 (by linarith [ht.out] : -t < 0)
        simpa using this
      rw [h1] at hr
      simp at hr
    exact this.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_G_le hz ht

/-- **Gauss's integral for the digamma function.** For `Re z > 0`,
`ψ(z) = -γ + ∫₀^∞ (e^{-t} - e^{-z t}) / (1 - e^{-t}) dt`. -/
theorem digamma_eq_integral {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z = -(Real.eulerMascheroniConstant : ℂ) +
      ∫ t : ℝ in Ioi 0, (Complex.exp (-(t : ℂ)) - Complex.exp (-z * t)) /
        (1 - Complex.exp (-(t : ℂ))) := by
  have hpoles : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  rw [← GppDigammaGaussSeries.digammaSeries_eq_digamma hpoles]
  have hsum := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := fun n : ℕ => F z n)
    (fun n => integrableOn_F hz n) (summable_integral_norm_F hz)
  have hterm : ∀ n : ℕ, ∫ t : ℝ in Ioi 0, F z n t = GppDigammaSeries.digammaSeriesTerm z n :=
    fun n => integral_F hz n
  have htsum : ∑' n : ℕ, GppDigammaSeries.digammaSeriesTerm z n =
      ∫ t : ℝ in Ioi 0, G z t := by
    have h1 := hsum.tsum_eq
    simp only [hterm] at h1
    rw [h1]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    exact tsum_F_eq ht
  unfold GppDigammaSeries.digammaSeries
  rw [htsum]
  have hexp : ∫ t : ℝ in Ioi 0, Complex.exp (-z * t) = z⁻¹ := integral_exp_neg hz
  have hint : ∫ t : ℝ in Ioi 0, (G z t - Complex.exp (-z * t)) =
      (∫ t : ℝ in Ioi 0, G z t) - z⁻¹ := by
    rw [integral_sub (integrableOn_G hz.le) (integrableOn_exp_neg hz), hexp]
  have hcongr : ∫ t : ℝ in Ioi 0, (Complex.exp (-(t : ℂ)) - Complex.exp (-z * t)) /
        (1 - Complex.exp (-(t : ℂ))) = ∫ t : ℝ in Ioi 0, (G z t - Complex.exp (-z * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : 0 < t := ht
    have hne : (1 - Complex.exp (-(t : ℂ))) ≠ 0 := by
      intro h
      have h1 : Complex.exp (-(t : ℂ)) = 1 := by linear_combination -h
      have hr : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
        rw [Complex.norm_exp]
        have := Real.exp_lt_exp.2 (by linarith : -t < 0)
        simpa using this
      rw [h1] at hr
      simp at hr
    simp only [G]
    field_simp
    ring
  rw [hcongr, hint]
  ring

end GppDigammaIntegral
