import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Continuous sech Lévy kernel algebra

This file isolates the exact algebraic kernel suggested by the Lévy–Khintchine
representation of the continuous chamber transform

  `Phi_c(t) = sech(t/2)^(2c)`.

For `x ≠ 0`, the candidate symmetric Lévy density is

  `nu_c(x) = c / (|x| * sinh(pi * |x|))`.

The analytic identity

  `log Phi_c(t) = ∫ (cos(t*x)-1) nu_c(x) dx`

is deliberately *not* asserted here.  The present file formalizes only the
parameter-additive, reflection, pointwise sign, and elementary majorant
properties of the candidate density and its Lévy exponent kernel.  These are
reusable prerequisites for a later Lévy-integrability and integral-identification
theorem.

Important analytic boundary: `nu_c(x)` behaves like `c / (pi * x^2)` at the
origin, so the density itself is not locally integrable there for `c > 0`.
The correct target is the Lévy condition for `(1 ∧ x^2) * nu_c(x)`, or,
equivalently for the exponent calculation, local integrability after the
quadratic cancellation in `1 - cos(t*x)`.
-/

namespace GppContinuousSechLevyKernel

/-- Candidate symmetric Lévy density for continuous chamber parameter `c`. -/
noncomputable def levyDensity (c x : ℝ) : ℝ :=
  c / (|x| * Real.sinh (Real.pi * |x|))

/-- Pointwise symmetric Lévy exponent kernel. -/
noncomputable def levyExponentKernel (c t x : ℝ) : ℝ :=
  (Real.cos (t * x) - 1) * levyDensity c x

/-- Positive-sign compensated kernel used in the Lévy integral. -/
noncomputable def compensatedLevyKernel (c t x : ℝ) : ℝ :=
  (1 - Real.cos (t * x)) * levyDensity c x

/-- The candidate Lévy density is exactly additive in the chamber parameter. -/
theorem levyDensity_add (c d x : ℝ) :
    levyDensity (c + d) x = levyDensity c x + levyDensity d x := by
  unfold levyDensity
  exact add_div c d (|x| * Real.sinh (Real.pi * |x|))

/-- The zero chamber parameter has zero candidate Lévy density. -/
theorem levyDensity_zero (x : ℝ) : levyDensity 0 x = 0 := by
  simp [levyDensity]

/-- At the spatial origin Lean's totalized division gives the removable value zero. -/
theorem levyDensity_at_zero (c : ℝ) : levyDensity c 0 = 0 := by
  simp [levyDensity]

/-- The candidate Lévy density is spatially even. -/
theorem levyDensity_neg (c x : ℝ) : levyDensity c (-x) = levyDensity c x := by
  simp [levyDensity]

/-- Away from the origin, a positive chamber parameter gives a strictly positive Lévy density. -/
theorem levyDensity_pos {c x : ℝ} (hc : 0 < c) (hx : x ≠ 0) :
    0 < levyDensity c x := by
  unfold levyDensity
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hsinh : 0 < Real.sinh (Real.pi * |x|) := by
    exact Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hxabs)
  exact div_pos hc (mul_pos hxabs hsinh)

/-- Away from the origin, a nonnegative chamber parameter gives a nonnegative Lévy density. -/
theorem levyDensity_nonneg {c x : ℝ} (hc : 0 ≤ c) (hx : x ≠ 0) :
    0 ≤ levyDensity c x := by
  unfold levyDensity
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hsinh : 0 < Real.sinh (Real.pi * |x|) := by
    exact Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hxabs)
  exact div_nonneg hc (le_of_lt (mul_pos hxabs hsinh))

/-- A nonnegative chamber parameter gives a globally nonnegative totalized density. -/
theorem levyDensity_nonneg_global {c x : ℝ} (hc : 0 ≤ c) :
    0 ≤ levyDensity c x := by
  by_cases hx : x = 0
  · subst x
    rw [levyDensity_at_zero]
  · exact levyDensity_nonneg hc hx

/-- The quadratic compensation has the global elementary majorant `c / pi`.
This is stronger than a merely local bound and is the near-origin half of the
Lévy weighted-integrability estimate. -/
theorem sq_abs_mul_levyDensity_le {c x : ℝ} (hc : 0 ≤ c) :
    |x| ^ 2 * levyDensity c x ≤ c / Real.pi := by
  by_cases hx : x = 0
  · subst x
    simp only [levyDensity, abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul]
    exact div_nonneg hc Real.pi_pos.le
  · have hxabs : 0 < |x| := abs_pos.mpr hx
    have harg : 0 ≤ Real.pi * |x| := le_of_lt (mul_pos Real.pi_pos hxabs)
    have hsinhLower : Real.pi * |x| ≤ Real.sinh (Real.pi * |x|) :=
      (Real.self_le_sinh_iff).2 harg
    have hsinh : 0 < Real.sinh (Real.pi * |x|) :=
      Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hxabs)
    have hden : 0 < |x| * Real.sinh (Real.pi * |x|) := mul_pos hxabs hsinh
    have hscaled :
        (c * |x|) * (Real.pi * |x|) ≤
          (c * |x|) * Real.sinh (Real.pi * |x|) :=
      mul_le_mul_of_nonneg_left hsinhLower (mul_nonneg hc (abs_nonneg x))
    unfold levyDensity
    rw [← mul_div_assoc]
    rw [div_le_div_iff₀ hden Real.pi_pos]
    calc
      (|x| ^ 2 * c) * Real.pi = (c * |x|) * (Real.pi * |x|) := by ring
      _ ≤ (c * |x|) * Real.sinh (Real.pi * |x|) := hscaled
      _ = c * (|x| * Real.sinh (Real.pi * |x|)) := by ring

/-- The pointwise Lévy exponent kernel is additive in the chamber parameter. -/
theorem levyExponentKernel_add (c d t x : ℝ) :
    levyExponentKernel (c + d) t x =
      levyExponentKernel c t x + levyExponentKernel d t x := by
  unfold levyExponentKernel
  rw [levyDensity_add]
  ring

/-- Frequency reflection leaves the pointwise Lévy exponent kernel unchanged. -/
theorem levyExponentKernel_neg_frequency (c t x : ℝ) :
    levyExponentKernel c (-t) x = levyExponentKernel c t x := by
  unfold levyExponentKernel
  rw [show (-t) * x = -(t * x) by ring, Real.cos_neg]

/-- Spatial reflection leaves the pointwise Lévy exponent kernel unchanged. -/
theorem levyExponentKernel_neg_space (c t x : ℝ) :
    levyExponentKernel c t (-x) = levyExponentKernel c t x := by
  unfold levyExponentKernel
  rw [levyDensity_neg]
  rw [show t * (-x) = -(t * x) by ring, Real.cos_neg]

/-- For nonnegative chamber parameter, the pointwise Lévy exponent kernel is nonpositive away from zero. -/
theorem levyExponentKernel_nonpos {c t x : ℝ} (hc : 0 ≤ c) (hx : x ≠ 0) :
    levyExponentKernel c t x ≤ 0 := by
  unfold levyExponentKernel
  have hcos : Real.cos (t * x) - 1 ≤ 0 := sub_nonpos.mpr (Real.cos_le_one (t * x))
  have hnu : 0 ≤ levyDensity c x := levyDensity_nonneg hc hx
  exact mul_nonpos_of_nonpos_of_nonneg hcos hnu

/-- The totalized pointwise Lévy exponent kernel is globally nonpositive. -/
theorem levyExponentKernel_nonpos_global {c t x : ℝ} (hc : 0 ≤ c) :
    levyExponentKernel c t x ≤ 0 := by
  unfold levyExponentKernel
  have hcos : Real.cos (t * x) - 1 ≤ 0 := sub_nonpos.mpr (Real.cos_le_one (t * x))
  have hnu : 0 ≤ levyDensity c x := levyDensity_nonneg_global hc
  exact mul_nonpos_of_nonpos_of_nonneg hcos hnu

/-- The positive-sign compensated kernel is exactly the negative exponent kernel. -/
theorem compensatedLevyKernel_eq_neg (c t x : ℝ) :
    compensatedLevyKernel c t x = -levyExponentKernel c t x := by
  unfold compensatedLevyKernel levyExponentKernel
  ring

/-- The compensated kernel is additive in the chamber parameter. -/
theorem compensatedLevyKernel_add (c d t x : ℝ) :
    compensatedLevyKernel (c + d) t x =
      compensatedLevyKernel c t x + compensatedLevyKernel d t x := by
  unfold compensatedLevyKernel
  rw [levyDensity_add]
  ring

/-- Frequency reflection leaves the compensated kernel unchanged. -/
theorem compensatedLevyKernel_neg_frequency (c t x : ℝ) :
    compensatedLevyKernel c (-t) x = compensatedLevyKernel c t x := by
  unfold compensatedLevyKernel
  rw [show (-t) * x = -(t * x) by ring, Real.cos_neg]

/-- Spatial reflection leaves the compensated kernel unchanged. -/
theorem compensatedLevyKernel_neg_space (c t x : ℝ) :
    compensatedLevyKernel c t (-x) = compensatedLevyKernel c t x := by
  unfold compensatedLevyKernel
  rw [levyDensity_neg]
  rw [show t * (-x) = -(t * x) by ring, Real.cos_neg]

/-- For nonnegative chamber parameter, the compensated Lévy kernel is globally nonnegative. -/
theorem compensatedLevyKernel_nonneg {c t x : ℝ} (hc : 0 ≤ c) :
    0 ≤ compensatedLevyKernel c t x := by
  unfold compensatedLevyKernel
  have hcos : 0 ≤ 1 - Real.cos (t * x) := sub_nonneg.mpr (Real.cos_le_one (t * x))
  have hnu : 0 ≤ levyDensity c x := levyDensity_nonneg_global hc
  exact mul_nonneg hcos hnu

/-- The compensated kernel is globally dominated by twice the Lévy density.
This is the tail-side elementary majorant: it combines with exponential decay
of `levyDensity` away from the origin. -/
theorem compensatedLevyKernel_le_two_mul_density {c t x : ℝ} (hc : 0 ≤ c) :
    compensatedLevyKernel c t x ≤ 2 * levyDensity c x := by
  unfold compensatedLevyKernel
  have hcos : 1 - Real.cos (t * x) ≤ 2 := by
    linarith [Real.neg_one_le_cos (t * x)]
  have hnu : 0 ≤ levyDensity c x := levyDensity_nonneg_global hc
  exact mul_le_mul_of_nonneg_right hcos hnu

/-- Quadratic cancellation makes the compensated kernel globally bounded.
The exact bound `t^2 c / (2 pi)` is the near-origin domination needed for the
Lévy integral, obtained from `1 - cos y ≤ y^2/2` and the global quadratic
density majorant above. -/
theorem compensatedLevyKernel_le_uniform {c t x : ℝ} (hc : 0 ≤ c) :
    compensatedLevyKernel c t x ≤ t ^ 2 * c / (2 * Real.pi) := by
  unfold compensatedLevyKernel
  have hcos : 1 - Real.cos (t * x) ≤ (t * x) ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := t * x)]
  have hnu : 0 ≤ levyDensity c x := levyDensity_nonneg_global hc
  have hfirst :
      (1 - Real.cos (t * x)) * levyDensity c x ≤
        ((t * x) ^ 2 / 2) * levyDensity c x :=
    mul_le_mul_of_nonneg_right hcos hnu
  have hsq := sq_abs_mul_levyDensity_le (c := c) (x := x) hc
  have hscale : 0 ≤ t ^ 2 / 2 := by positivity
  have hsecond := mul_le_mul_of_nonneg_left hsq hscale
  calc
    (1 - Real.cos (t * x)) * levyDensity c x
        ≤ ((t * x) ^ 2 / 2) * levyDensity c x := hfirst
    _ = (t ^ 2 / 2) * (|x| ^ 2 * levyDensity c x) := by rw [sq_abs]; ring
    _ ≤ (t ^ 2 / 2) * (c / Real.pi) := hsecond
    _ = t ^ 2 * c / (2 * Real.pi) := by field_simp [Real.pi_ne_zero]

/-- The compensated kernel vanishes at the spatial origin under totalized division. -/
theorem compensatedLevyKernel_at_zero (c t : ℝ) :
    compensatedLevyKernel c t 0 = 0 := by
  simp [compensatedLevyKernel, levyDensity_at_zero]

end GppContinuousSechLevyKernel

#print axioms GppContinuousSechLevyKernel.levyDensity_add
#print axioms GppContinuousSechLevyKernel.levyDensity_at_zero
#print axioms GppContinuousSechLevyKernel.levyDensity_pos
#print axioms GppContinuousSechLevyKernel.levyDensity_nonneg
#print axioms GppContinuousSechLevyKernel.levyDensity_nonneg_global
#print axioms GppContinuousSechLevyKernel.sq_abs_mul_levyDensity_le
#print axioms GppContinuousSechLevyKernel.levyExponentKernel_add
#print axioms GppContinuousSechLevyKernel.levyExponentKernel_neg_frequency
#print axioms GppContinuousSechLevyKernel.levyExponentKernel_neg_space
#print axioms GppContinuousSechLevyKernel.levyExponentKernel_nonpos
#print axioms GppContinuousSechLevyKernel.levyExponentKernel_nonpos_global
#print axioms GppContinuousSechLevyKernel.compensatedLevyKernel_eq_neg
#print axioms GppContinuousSechLevyKernel.compensatedLevyKernel_add
#print axioms GppContinuousSechLevyKernel.compensatedLevyKernel_neg_frequency
#print axioms GppContinuousSechLevyKernel.compensatedLevyKernel_neg_space
#print axioms GppContinuousSechLevyKernel.compensatedLevyKernel_nonneg
#print axioms GppContinuousSechLevyKernel.compensatedLevyKernel_le_two_mul_density
#print axioms GppContinuousSechLevyKernel.compensatedLevyKernel_le_uniform
#print axioms GppContinuousSechLevyKernel.compensatedLevyKernel_at_zero
