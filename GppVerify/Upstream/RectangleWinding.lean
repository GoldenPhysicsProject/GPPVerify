/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The winding number of a rectangle

For a point `ρ` strictly inside a rectangle, the boundary integral of `1 / (s - ρ)`, in the
orientation and notation of `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, is
`2 π i`. Mathlib has Cauchy's theorem for rectangles with a holomorphic interior and circle
integrals, but no residue or winding-number statement for rectangles.

The proof computes the four edges with logarithmic antiderivatives. Three of the four edges stay in
the slit plane; on the left edge `Re (s - ρ) < 0`, so we use `log (-(s - ρ))`. The corner terms
telescope, leaving `log w - log (-w)` at the two ends of the left edge, which is `+ π i` for
`Im w > 0` and `- π i` for `Im w < 0`.
-/

open Complex Set intervalIntegral

namespace Complex

/-- `log w - log (-w) = π i` for `Im w > 0` and `-π i` for `Im w < 0`. -/
theorem log_sub_log_neg_of_im_pos {w : ℂ} (h : 0 < w.im) : log w - log (-w) = (Real.pi : ℂ) * I := by
  have h0 : w ≠ 0 := fun h' => by simp [h'] at h
  rw [log, log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos h]
  push_cast
  ring

theorem log_sub_log_neg_of_im_neg {w : ℂ} (h : w.im < 0) : log w - log (-w) = -((Real.pi : ℂ) * I) := by
  have h0 : w ≠ 0 := fun h' => by simp [h'] at h
  rw [log, log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg h]
  push_cast
  ring

/-- Horizontal edge of the rectangle: the integral of `1 / (s - ρ)` along `Im s = y ≠ Im ρ`. -/
theorem integral_inv_sub_horizontal (ρ : ℂ) {y : ℝ} (hy : y ≠ ρ.im) (x₁ x₂ : ℝ) :
    ∫ x : ℝ in x₁..x₂, ((x : ℂ) + y * I - ρ)⁻¹ =
      log ((x₂ : ℂ) + y * I - ρ) - log ((x₁ : ℂ) + y * I - ρ) := by
  have hne : ∀ x : ℝ, (x : ℂ) + y * I - ρ ≠ 0 := by
    intro x h
    have := congrArg Complex.im h
    simp at this
    exact hy (by linarith)
  have hslit : ∀ x : ℝ, (x : ℂ) + y * I - ρ ∈ slitPlane := by
    intro x
    rw [mem_slitPlane_iff]
    right
    simp
    intro h; exact hy (by linarith)
  have hd : ∀ x ∈ uIcc x₁ x₂, HasDerivAt (fun x : ℝ => log ((x : ℂ) + y * I - ρ))
      (((x : ℂ) + y * I - ρ)⁻¹) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) + y * I - ρ) 1 x :=
      ((hasDerivAt_id x).ofReal_comp.add_const _).sub_const _
    simpa [one_div] using h1.clog_real (hslit x)
  refine integral_eq_sub_of_hasDerivAt hd ?_
  refine Continuous.intervalIntegrable ?_ _ _
  exact Continuous.inv₀ (by fun_prop) hne

/-- Right edge (`Re s > Re ρ`). -/
theorem I_mul_integral_inv_sub_right (ρ : ℂ) {x : ℝ} (hx : ρ.re < x) (y₁ y₂ : ℝ) :
    I * ∫ y : ℝ in y₁..y₂, ((x : ℂ) + y * I - ρ)⁻¹ =
      log ((x : ℂ) + y₂ * I - ρ) - log ((x : ℂ) + y₁ * I - ρ) := by
  have hne : ∀ y : ℝ, (x : ℂ) + y * I - ρ ≠ 0 := by
    intro y h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hslit : ∀ y : ℝ, (x : ℂ) + y * I - ρ ∈ slitPlane := by
    intro y
    rw [mem_slitPlane_iff]
    left
    simp
    linarith
  have hd : ∀ y ∈ uIcc y₁ y₂, HasDerivAt (fun y : ℝ => log ((x : ℂ) + y * I - ρ))
      (I * ((x : ℂ) + y * I - ρ)⁻¹) y := by
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => (x : ℂ) + y * I - ρ) I y := by
      have := ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (x : ℂ)
      simpa using this.sub_const ρ
    simpa [div_eq_mul_inv] using h1.clog_real (hslit y)
  rw [← intervalIntegral.integral_const_mul]
  refine integral_eq_sub_of_hasDerivAt hd ?_
  refine Continuous.intervalIntegrable ?_ _ _
  exact continuous_const.mul (Continuous.inv₀ (by fun_prop) hne)

/-- Left edge (`Re s < Re ρ`): the branch `log (-(s - ρ))`. -/
theorem I_mul_integral_inv_sub_left (ρ : ℂ) {x : ℝ} (hx : x < ρ.re) (y₁ y₂ : ℝ) :
    I * ∫ y : ℝ in y₁..y₂, ((x : ℂ) + y * I - ρ)⁻¹ =
      log (-((x : ℂ) + y₂ * I - ρ)) - log (-((x : ℂ) + y₁ * I - ρ)) := by
  have hne : ∀ y : ℝ, (x : ℂ) + y * I - ρ ≠ 0 := by
    intro y h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hslit : ∀ y : ℝ, -((x : ℂ) + y * I - ρ) ∈ slitPlane := by
    intro y
    rw [mem_slitPlane_iff]
    left
    simp
    linarith
  have hd : ∀ y ∈ uIcc y₁ y₂, HasDerivAt (fun y : ℝ => log (-((x : ℂ) + y * I - ρ)))
      (I * ((x : ℂ) + y * I - ρ)⁻¹) y := by
    intro y _
    have h0 : HasDerivAt (fun y : ℝ => (x : ℂ) + y * I - ρ) I y := by
      have := ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (x : ℂ)
      simpa using this.sub_const ρ
    have h1 : HasDerivAt (fun y : ℝ => -((x : ℂ) + y * I - ρ)) (-I) y := h0.neg
    have h2 := h1.clog_real (hslit y)
    convert h2 using 1
    have := hne y
    field_simp
  rw [← intervalIntegral.integral_const_mul]
  refine integral_eq_sub_of_hasDerivAt hd ?_
  refine Continuous.intervalIntegrable ?_ _ _
  exact continuous_const.mul (Continuous.inv₀ (by fun_prop) hne)

/-- **Winding number of a rectangle.** For `ρ` strictly inside the rectangle with corners `z` and
`w`, the boundary integral of `1 / (s - ρ)`, in the notation of
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, equals `2 π i`. -/
theorem rect_boundary_integral_inv_sub {z w ρ : ℂ} (hzr : z.re < ρ.re) (hrw : ρ.re < w.re)
    (hzi : z.im < ρ.im) (hiw : ρ.im < w.im) :
    (∫ x : ℝ in z.re..w.re, (fun s : ℂ => (s - ρ)⁻¹) (x + z.im * I)) -
      (∫ x : ℝ in z.re..w.re, (fun s : ℂ => (s - ρ)⁻¹) (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, (fun s : ℂ => (s - ρ)⁻¹) (w.re + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, (fun s : ℂ => (s - ρ)⁻¹) (z.re + y * I)) =
      2 * Real.pi * I := by
  simp only [smul_eq_mul]
  rw [integral_inv_sub_horizontal ρ hzi.ne z.re w.re, integral_inv_sub_horizontal ρ hiw.ne' z.re w.re,
    I_mul_integral_inv_sub_right ρ hrw z.im w.im, I_mul_integral_inv_sub_left ρ hzr z.im w.im]
  have h2 : log (-(((z.re : ℝ) : ℂ) + (w.im : ℂ) * I - ρ)) - 
      log (-(((z.re : ℝ) : ℂ) + (z.im : ℂ) * I - ρ)) =
      log (((z.re : ℝ) : ℂ) + (w.im : ℂ) * I - ρ) - (Real.pi : ℂ) * I -
      (log (((z.re : ℝ) : ℂ) + (z.im : ℂ) * I - ρ) + (Real.pi : ℂ) * I) := by
    have a1 := log_sub_log_neg_of_im_pos (w := ((z.re : ℝ) : ℂ) + (w.im : ℂ) * I - ρ) (by simp; linarith)
    have a2 := log_sub_log_neg_of_im_neg (w := ((z.re : ℝ) : ℂ) + (z.im : ℂ) * I - ρ) (by simp; linarith)
    linear_combination -a1 + a2
  linear_combination (-1 : ℂ) * h2

end Complex
