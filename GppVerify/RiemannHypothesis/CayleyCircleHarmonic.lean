import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Cayley circle: disk faces, boundary parametrization, and harmonic measure based at `s = 1`

Source: Codex, GPP-bridge `work/codex/2026-10-13_cayley_mirror_circle_infinite_length.md` and
`…_cayley_circle_haar_harmonic_measure.md` (PR #11 comment 6159461017).

With the canonical Cayley coordinate `w = β(s) = (s − 1)/s` (the shadow/inverse and unit-norm-on-line
facts are already in `CayleyShadowAdjointBridge`), this file proves:
* `norm_beta_lt_one_iff`: `|w| < 1 ⟺ Re s > ½` (and `norm_beta_gt_one_iff` for `Re s < ½`). The
  two disk faces are the two half-planes, glued along the circle `|w| = 1`, which is the critical line.
* `beta_line`: on the line, `β(½ + iγ) = −exp(−2i·arctan(2γ))`, so `θ(γ) = π − 2 arctan(2γ)` is
  the boundary angle.
* `hasDerivAt_angle`: `d/dγ [2 arctan(2γ)] = 1/(γ² + ¼)`. So the normalized circle Haar measure
  `dθ/2π` pulls back to `dγ / (2π(γ² + ¼))`, which is the Poisson kernel (harmonic measure) of the
  half-plane `Re s > ½` based at `s = 1`, the image of the disk center `w = 0`.
* `harmonic_mass_one`: `∫_ℝ dγ / (2π(γ² + ¼)) = 1`, a probability measure. This is unlike the
  infinite translation-invariant `dγ` on the line, which is the infinite "inherited arclength"
  of Codex's note.

Gluing the two disks along the circle gives the Riemann sphere, which is real dimension 2. Nothing
here makes a 4-dimensional bulk. **No RH claim.**
-/

namespace GppCayleyCircleHarmonic

open Complex Real

/-- The Cayley coordinate `β(s) = (s − 1)/s`. -/
noncomputable def beta (s : ℂ) : ℂ := (s - 1) / s

theorem norm_sub_one_lt_iff (s : ℂ) : ‖s - 1‖ < ‖s‖ ↔ 1 / 2 < s.re := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  constructor <;> intro h <;> nlinarith

theorem norm_sub_one_gt_iff (s : ℂ) : ‖s‖ < ‖s - 1‖ ↔ s.re < 1 / 2 := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  constructor <;> intro h <;> nlinarith

/-- **Inner face**: `|β(s)| < 1 ⟺ Re s > ½`. -/
theorem norm_beta_lt_one_iff {s : ℂ} (hs : s ≠ 0) : ‖beta s‖ < 1 ↔ 1 / 2 < s.re := by
  rw [beta, norm_div, div_lt_one (norm_pos_iff.mpr hs), norm_sub_one_lt_iff]

/-- **Outer face**: `|β(s)| > 1 ⟺ Re s < ½`. -/
theorem norm_beta_gt_one_iff {s : ℂ} (hs : s ≠ 0) : 1 < ‖beta s‖ ↔ s.re < 1 / 2 := by
  rw [beta, norm_div, one_lt_div (norm_pos_iff.mpr hs), norm_sub_one_gt_iff]

/-- **Boundary parametrization**: `β(½ + iγ) = −exp(−2i·arctan(2γ))`. -/
theorem beta_line (γ : ℝ) :
    beta (1 / 2 + γ * I) = -exp (-(2 * (Real.arctan (2 * γ) : ℂ) * I)) := by
  set φ := Real.arctan (2 * γ) with hφ
  set q := Real.sqrt (1 + (2 * γ) ^ 2) with hqdef
  have hq : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hq2 : (q : ℂ) ^ 2 = 1 + 4 * (γ : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, hqdef, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hc : Real.cos φ = 1 / q := by rw [hφ, Real.cos_arctan]
  have hs : Real.sin φ = 2 * γ / q := by rw [hφ, Real.sin_arctan]
  have he : exp (-(2 * (φ : ℂ) * I)) = (exp (((-φ : ℝ) : ℂ) * I)) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg, hc, hs]
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hz : (1 / 2 + (γ : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  unfold beta
  rw [div_eq_iff hz]
  push_cast
  field_simp
  linear_combination (2 * γ * I - 1) * hq2 + (-4 * (γ : ℂ) ^ 2 + 8 * γ ^ 3 * I) * Complex.I_sq

/-- **Pulled-back circle Haar density**: `d/dγ [2 arctan(2γ)] = 1/(γ² + ¼)`. -/
theorem hasDerivAt_angle (γ : ℝ) :
    HasDerivAt (fun g : ℝ => 2 * Real.arctan (2 * g)) (1 / (γ ^ 2 + 1 / 4)) γ := by
  have h := ((hasDerivAt_id γ).const_mul 2).arctan
  have h2 := h.const_mul 2
  refine h2.congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- **Harmonic measure is a probability measure**: `∫_ℝ dγ / (2π(γ² + ¼)) = 1`. -/
theorem harmonic_mass_one :
    ∫ γ : ℝ, 1 / (2 * π * (γ ^ 2 + 1 / 4)) = 1 := by
  have key : ∫ γ : ℝ, (1 + (2 * γ) ^ 2)⁻¹ = π / 2 := by
    rw [MeasureTheory.Measure.integral_comp_mul_left (fun x => (1 + x ^ 2)⁻¹) 2,
      integral_univ_inv_one_add_sq]
    simp; ring
  have hfun : (fun γ : ℝ => 1 / (2 * π * (γ ^ 2 + 1 / 4))) =
      fun γ => (2 / π) * (1 + (2 * γ) ^ 2)⁻¹ := by
    funext γ
    have : (0 : ℝ) < 1 + (2 * γ) ^ 2 := by positivity
    field_simp
    ring
  rw [hfun, MeasureTheory.integral_const_mul, key]
  field_simp

end GppCayleyCircleHarmonic
