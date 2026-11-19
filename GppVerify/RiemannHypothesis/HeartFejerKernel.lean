/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Tactic
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Fejér kernel facts (Heart claim #31, `HR22_fejer_kernel_facts`)

For `L > 0` let `K(r) = (L / 2π) · sinc(rL/2)²` (the Fejér kernel; `Real.sinc` is Mathlib's
`sin x / x`, with value `1` at `0`) and let `Δ_L(x) = max (1 − |x|/L) 0` be the triangle function.

* `fejerK_nonneg`: `K ≥ 0`;
* `fourier_triangle`: the Fourier transform of the triangle is `L · sinc(aL/2)²`, i.e.
  `∫ Δ_L(x) e^{−iax} dx = L · sinc(aL/2)²` for every real `a`;
* `integral_fejerK`: `∫ K = 1`;
* `fejerK_fourier`: `K̂(x) = ∫ K(r) e^{−irx} dr = (1 − |x|/L)₊` (and the cosine form).

`∫ K = 1` and the inversion `K̂ = Δ_L` are obtained from Mathlib's Fourier inversion theorem
(`Continuous.fourierInv_fourier_eq`) applied to the triangle, so no improper integral of `sinc²` is
computed directly. No `sorry`, no `axiom`.
-/

namespace GppFejer

open MeasureTheory Set Real
open scoped Real

/-- The Fejér kernel `K_L(r) = (L / 2π) sinc(rL/2)²`. -/
noncomputable def fejerK (L r : ℝ) : ℝ := L / (2 * π) * Real.sinc (r * L / 2) ^ 2

/-- The triangle function `max (1 − |x|/L) 0`. -/
noncomputable def tri (L x : ℝ) : ℝ := max (1 - |x| / L) 0

theorem fejerK_nonneg {L : ℝ} (hL : 0 ≤ L) (r : ℝ) : 0 ≤ fejerK L r := by
  unfold fejerK
  positivity

theorem tri_nonneg (L x : ℝ) : 0 ≤ tri L x := le_max_right _ _

theorem continuous_tri {L : ℝ} : Continuous (tri L) := by
  unfold tri
  fun_prop

theorem tri_of_abs_ge {L x : ℝ} (hL : 0 < L) (hx : L ≤ |x|) : tri L x = 0 := by
  unfold tri
  have : 1 - |x| / L ≤ 0 := by
    rw [sub_nonpos, one_le_div hL]; exact hx
  exact max_eq_right this

/-! ### The cosine moment of `1 − x/L` on `[0, L]` -/

theorem integral_linear_cos {L a : ℝ} (hL : 0 < L) :
    ∫ x in (0 : ℝ)..L, (1 - x / L) * Real.cos (a * x) = L / 2 * Real.sinc (a * L / 2) ^ 2 := by
  by_cases ha : a = 0
  · subst ha
    simp only [zero_mul, Real.cos_zero, mul_one, zero_mul]
    rw [intervalIntegral.integral_sub (by simp) (by simp)]
    simp
    field_simp
    ring
  · have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) L, HasDerivAt
        (fun x => (1 - x / L) * Real.sin (a * x) / a - Real.cos (a * x) / (L * a ^ 2))
        ((1 - x / L) * Real.cos (a * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun x : ℝ => 1 - x / L) (-(1 / L)) x := by
        have := ((hasDerivAt_id x).div_const L).const_sub 1
        simpa using this
      have h2 : HasDerivAt (fun x : ℝ => Real.sin (a * x)) (Real.cos (a * x) * a) x := by
        have := ((hasDerivAt_id x).const_mul a).sin
        simpa using this
      have h3 : HasDerivAt (fun x : ℝ => Real.cos (a * x)) (-Real.sin (a * x) * a) x := by
        have := ((hasDerivAt_id x).const_mul a).cos
        simpa using this
      have := ((h1.mul h2).div_const a).sub (h3.div_const (L * a ^ 2))
      have hL0 : L ≠ 0 := hL.ne'
      exact this.congr_deriv (by field_simp; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (by apply Continuous.intervalIntegrable; fun_prop)]
    have hLa : a * L / 2 ≠ 0 := by positivity
    rw [Real.sinc_of_ne_zero hLa]
    have hc : Real.cos (a * L) = 1 - 2 * Real.sin (a * L / 2) ^ 2 := by
      have h2 := Real.cos_two_mul (a * L / 2)
      have h3 := Real.sin_sq_add_cos_sq (a * L / 2)
      have e : 2 * (a * L / 2) = a * L := by ring
      rw [e] at h2
      rw [h2]; nlinarith [h3]
    simp only [mul_zero, Real.sin_zero, sub_zero, Real.cos_zero, div_self hL.ne',
      sub_self, zero_mul, zero_div, zero_sub]
    have hL0 : L ≠ 0 := hL.ne'
    rw [hc]
    field_simp
    ring


/-! ### The Fourier transform of the triangle -/

open Complex in
theorem fourier_triangle {L : ℝ} (hL : 0 < L) (a : ℝ) :
    ∫ v : ℝ, Complex.exp (((-a * v : ℝ) : ℂ) * Complex.I) • ((tri L v : ℝ) : ℂ)
      = ((L * Real.sinc (a * L / 2) ^ 2 : ℝ) : ℂ) := by
  set g : ℝ → ℂ := fun v => Complex.exp (((-a * v : ℝ) : ℂ) * Complex.I) • ((tri L v : ℝ) : ℂ)
    with hg
  have hgc : Continuous g := by
    have := continuous_tri (L := L)
    simp only [hg, smul_eq_mul]
    fun_prop
  -- support in (-L, L]
  have hsupp : ∀ v ∉ Set.Ioc (-L) L, g v = 0 := by
    intro v hv
    have : L ≤ |v| := by
      by_contra h
      rw [not_le] at h
      exact hv ⟨by linarith [abs_lt.mp h], by linarith [abs_lt.mp h]⟩
    simp [hg, tri_of_abs_ge hL this]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    ← intervalIntegral.integral_of_le (by linarith : -L ≤ L)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)]
  -- right half
  have hR : ∫ v in (0 : ℝ)..L, g v
      = ∫ v in (0 : ℝ)..L, Complex.exp (((-a * v : ℝ) : ℂ) * Complex.I) * (((1 - v / L : ℝ)) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le hL.le] at hv
    simp only [hg, smul_eq_mul, tri]
    have : 0 ≤ 1 - |v| / L := by
      rw [abs_of_nonneg hv.1, sub_nonneg, div_le_one hL]; exact hv.2
    rw [max_eq_left this, abs_of_nonneg hv.1]
  -- left half, reflected
  have hLf : ∫ v in (-L : ℝ)..0, g v
      = ∫ v in (0 : ℝ)..L, Complex.exp (((a * v : ℝ) : ℂ) * Complex.I) * (((1 - v / L : ℝ)) : ℂ) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := L) g
    rw [neg_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le hL.le] at hv
    simp only [hg, smul_eq_mul, tri, abs_neg]
    have : 0 ≤ 1 - |v| / L := by
      rw [abs_of_nonneg hv.1, sub_nonneg, div_le_one hL]; exact hv.2
    rw [max_eq_left this, abs_of_nonneg hv.1]
    congr 2
    push_cast
    ring
  rw [hLf, hR]
  have hc1 : Continuous fun v : ℝ => Complex.exp (((a * v : ℝ) : ℂ) * Complex.I) * (((1 - v / L : ℝ)) : ℂ) := by
    fun_prop
  have hc2 : Continuous fun v : ℝ => Complex.exp (((-a * v : ℝ) : ℂ) * Complex.I) * (((1 - v / L : ℝ)) : ℂ) := by
    fun_prop
  rw [← intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  have hcos : ∀ v : ℝ, Complex.exp (((a * v : ℝ) : ℂ) * Complex.I) * (((1 - v / L : ℝ)) : ℂ)
      + Complex.exp (((-a * v : ℝ) : ℂ) * Complex.I) * (((1 - v / L : ℝ)) : ℂ)
      = (((2 * ((1 - v / L) * Real.cos (a * v)) : ℝ)) : ℂ) := by
    intro v
    have h2 := Complex.two_cos (((a * v : ℝ) : ℂ))
    have e1 : (((-a * v : ℝ) : ℂ)) = -(((a * v : ℝ) : ℂ)) := by push_cast; ring
    rw [e1]
    have e2 : (((2 * ((1 - v / L) * Real.cos (a * v)) : ℝ)) : ℂ)
        = (((1 - v / L : ℝ)) : ℂ) * (2 * Complex.cos (((a * v : ℝ) : ℂ))) := by
      push_cast
      ring
    rw [e2, h2]
    have : -(((a * v : ℝ) : ℂ)) * Complex.I = -(((a * v : ℝ) : ℂ) * Complex.I) := by ring
    rw [this]
    ring
  simp_rw [hcos]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul, integral_linear_cos hL]
  push_cast
  ring


/-! ### Integrability -/

theorem sinc_sq_le (x : ℝ) : Real.sinc x ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have h1 : Real.sinc x ^ 2 ≤ 1 := by
    have := Real.abs_sinc_le_one x
    nlinarith [abs_nonneg (Real.sinc x), sq_abs (Real.sinc x)]
  have h2 : x ^ 2 * Real.sinc x ^ 2 ≤ 1 := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx, div_pow, ← mul_div_assoc, mul_comm, mul_div_assoc,
        div_self (pow_ne_zero 2 hx), mul_one]
      exact Real.sin_sq_le_one x
  have hpos : 0 < 1 + x ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  nlinarith

theorem integrable_sinc_sq_comp {c : ℝ} (hc : c ≠ 0) :
    Integrable (fun w : ℝ => Real.sinc (c * w) ^ 2) := by
  have hmeas : Continuous fun w : ℝ => Real.sinc (c * w) ^ 2 :=
    (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2
  have hint : Integrable fun w : ℝ => 2 * (1 + (c * w) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_mul_left' hc).const_mul 2
  refine hint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sinc_sq_le (c * w)

/-! ### Fourier inversion -/

open scoped FourierTransform in
theorem fourier_triangle_mathlib {L : ℝ} (hL : 0 < L) (w : ℝ) :
    𝓕 (fun x : ℝ => ((tri L x : ℝ) : ℂ)) w = ((L * Real.sinc (π * L * w) ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have := fourier_triangle hL (2 * π * w)
  have e : (2 * π * w * L / 2) = π * L * w := by ring
  rw [e] at this
  rw [← this]
  congr 1
  funext v
  congr 3
  push_cast
  ring

open scoped FourierTransform in
theorem fejer_inversion {L : ℝ} (hL : 0 < L) (v : ℝ) :
    ∫ w : ℝ, Complex.exp (((2 * π * w * v : ℝ) : ℂ) * Complex.I)
        * ((L * Real.sinc (π * L * w) ^ 2 : ℝ) : ℂ) = ((tri L v : ℝ) : ℂ) := by
  set f : ℝ → ℂ := fun x => ((tri L x : ℝ) : ℂ) with hf
  have hfc : Continuous f := Complex.continuous_ofReal.comp continuous_tri
  have hfi : Integrable f := by
    apply hfc.integrable_of_hasCompactSupport
    apply HasCompactSupport.intro (isCompact_Icc (a := -L) (b := L))
    intro x hx
    have : L ≤ |x| := by
      by_contra h
      rw [not_le] at h
      exact hx ⟨by linarith [abs_lt.mp h], by linarith [abs_lt.mp h]⟩
    simp [hf, tri_of_abs_ge hL this]
  have hF : 𝓕 f = fun w => ((L * Real.sinc (π * L * w) ^ 2 : ℝ) : ℂ) :=
    funext (fourier_triangle_mathlib hL)
  have hFi : Integrable (𝓕 f) := by
    rw [hF]
    have hc : π * L ≠ 0 := by positivity
    have h : Integrable (fun w : ℝ => L * Real.sinc (π * L * w) ^ 2) :=
      (integrable_sinc_sq_comp hc).const_mul L
    exact h.ofReal
  have hinv := congrFun (hfc.fourierInv_fourier_eq hfi hFi) v
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul, hF] at hinv
  simp only [hf] at hinv
  rw [← hinv]
  congr 1
  funext w
  simp only [smul_eq_mul]
  congr 3
  push_cast
  ring


/-! ### The Fejér kernel: normalisation and Fourier transform -/

/-- `∫ K(r) e^{irx} dr = (1 − |x|/L)₊`. -/
theorem fejerK_fourier_pos {L : ℝ} (hL : 0 < L) (x : ℝ) :
    ∫ r : ℝ, Complex.exp (((r * x : ℝ) : ℂ) * Complex.I) * ((fejerK L r : ℝ) : ℂ)
      = ((tri L x : ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun r =>
    Complex.exp (((r * x : ℝ) : ℂ) * Complex.I) * ((L * Real.sinc (r * L / 2) ^ 2 : ℝ) : ℂ) with hF
  have h1 := fejer_inversion hL x
  have h2 : ∫ w : ℝ, F (2 * π * w)
      = |(2 * π)⁻¹| • ∫ y : ℝ, F y :=
    MeasureTheory.Measure.integral_comp_mul_left F (2 * π)
  have hFw : ∀ w : ℝ, F (2 * π * w) = Complex.exp (((2 * π * w * x : ℝ) : ℂ) * Complex.I)
      * ((L * Real.sinc (π * L * w) ^ 2 : ℝ) : ℂ) := by
    intro w
    simp only [hF]
    have : 2 * π * w * L / 2 = π * L * w := by ring
    rw [this]
  simp_rw [hFw] at h2
  rw [h1] at h2
  have hπ : (0 : ℝ) < 2 * π := by positivity
  rw [abs_of_pos (inv_pos.mpr hπ)] at h2
  have h3 : ∫ y : ℝ, F y = ((2 * π : ℝ) : ℂ) * ((tri L x : ℝ) : ℂ) := by
    have : ((tri L x : ℝ) : ℂ) = ((2 * π)⁻¹ : ℝ) • ∫ y : ℝ, F y := h2
    rw [this, Complex.real_smul]
    push_cast
    field_simp
  have h4 : ∀ r : ℝ, Complex.exp (((r * x : ℝ) : ℂ) * Complex.I) * ((fejerK L r : ℝ) : ℂ)
      = ((1 / (2 * π) : ℝ) : ℂ) * F r := by
    intro r
    simp only [hF, fejerK]
    push_cast
    ring
  simp_rw [h4]
  rw [integral_const_mul, h3]
  push_cast
  field_simp

/-- `∫ K = 1`. -/
theorem integral_fejerK {L : ℝ} (hL : 0 < L) : ∫ r : ℝ, fejerK L r = 1 := by
  have h := fejerK_fourier_pos hL 0
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, tri,
    abs_zero, zero_div, sub_zero, max_eq_left zero_le_one, Complex.ofReal_one] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- `K̂(x) = ∫ K(r) e^{−irx} dr = (1 − |x|/L)₊`. -/
theorem fejerK_fourier {L : ℝ} (hL : 0 < L) (x : ℝ) :
    ∫ r : ℝ, Complex.exp (((-(r * x) : ℝ) : ℂ) * Complex.I) * ((fejerK L r : ℝ) : ℂ)
      = ((tri L x : ℝ) : ℂ) := by
  have h := fejerK_fourier_pos hL (-x)
  have e : tri L (-x) = tri L x := by simp [tri]
  rw [e] at h
  rw [← h]
  congr 1
  funext r
  congr 3
  push_cast
  ring

end GppFejer

#print axioms GppFejer.fourier_triangle
#print axioms GppFejer.fejer_inversion
#print axioms GppFejer.integral_fejerK
#print axioms GppFejer.fejerK_fourier
