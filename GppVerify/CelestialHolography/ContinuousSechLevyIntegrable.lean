import GppVerify.CelestialHolography.ContinuousSechLevyMeasurability
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Continuous sech Lévy compensated-kernel integrability

The certified core and inverse-square bounds can be compressed into one global
Cauchy majorant.  For `c ≥ 0`,

  K_c(t,x) ≤ C(c,t) / (1 + x^2),

with the deliberately generous constant

  C(c,t) = 2*c*(t^2 + 4)/pi.

Since `(1+x^2)⁻¹` is integrable on `ℝ`, this gives the first actual Lebesgue
`Integrable` theorem for the compensated Lévy exponent kernel.  No value for the
integral is asserted here.
-/

namespace GppContinuousSechLevyIntegrable

open MeasureTheory
open GppContinuousSechLevyKernel
open GppContinuousSechLevyTail
open GppContinuousSechLevyMeasurability

/-- A positive constant used for a global Cauchy-kernel majorant. -/
def cauchyMajorantConstant (c t : ℝ) : ℝ :=
  2 * c * (t ^ 2 + 4) / Real.pi

/-- The compensated kernel is globally dominated by an integrable Cauchy kernel. -/
theorem compensatedLevyKernel_le_cauchy {c t x : ℝ} (hc : 0 ≤ c) :
    compensatedLevyKernel c t x ≤
      cauchyMajorantConstant c t * (1 + x ^ 2)⁻¹ := by
  have hC : 0 ≤ cauchyMajorantConstant c t := by
    unfold cauchyMajorantConstant
    positivity
  have hden : 0 < 1 + x ^ 2 := by positivity
  by_cases hx : |x| ≤ 1
  · have hk := compensatedLevyKernel_le_uniform (c := c) (t := t) (x := x) hc
    have hx' := abs_le.mp hx
    have hden_le : 1 + x ^ 2 ≤ 2 := by
      nlinarith [sq_nonneg x]
    have hhalf : c * t ^ 2 / (2 * Real.pi) ≤ cauchyMajorantConstant c t / 2 := by
      unfold cauchyMajorantConstant
      have hpi : 0 < Real.pi := Real.pi_pos
      field_simp [ne_of_gt hpi]
      nlinarith [sq_nonneg t]
    have hdiv : cauchyMajorantConstant c t / 2 ≤
        cauchyMajorantConstant c t / (1 + x ^ 2) := by
      exact div_le_div_of_nonneg_left hC hden hden_le
    calc
      compensatedLevyKernel c t x ≤ c * t ^ 2 / (2 * Real.pi) := hk
      _ ≤ cauchyMajorantConstant c t / 2 := hhalf
      _ ≤ cauchyMajorantConstant c t / (1 + x ^ 2) := hdiv
      _ = cauchyMajorantConstant c t * (1 + x ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]
  · have hxgt : 1 < |x| := lt_of_not_ge hx
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      norm_num at hxgt
    have hk := compensatedLevyKernel_le_inv_sq (c := c) (t := t) (x := x) hc hx0
    have hx2 : 1 ≤ |x| ^ 2 := by nlinarith [sq_nonneg |x|]
    have hden_le : 1 + x ^ 2 ≤ 2 * |x| ^ 2 := by
      rw [sq_abs]
      nlinarith
    have htailconst : 2 * c / Real.pi ≤ cauchyMajorantConstant c t / 2 := by
      unfold cauchyMajorantConstant
      have hpi : 0 < Real.pi := Real.pi_pos
      field_simp [ne_of_gt hpi]
      nlinarith [sq_nonneg t]
    have hx2pos : 0 < |x| ^ 2 := by positivity
    have hstep1 : 2 * c / (Real.pi * |x| ^ 2) ≤
        (cauchyMajorantConstant c t / 2) / (|x| ^ 2) := by
      have := div_le_div_of_nonneg_right htailconst hx2pos.le
      simpa [div_div] using this
    have hstep2 : (cauchyMajorantConstant c t / 2) / (|x| ^ 2) ≤
        cauchyMajorantConstant c t / (1 + x ^ 2) := by
      have hnum : 0 ≤ cauchyMajorantConstant c t := hC
      have hleft : (cauchyMajorantConstant c t / 2) / (|x| ^ 2) =
          cauchyMajorantConstant c t / (2 * |x| ^ 2) := by ring
      rw [hleft]
      exact div_le_div_of_nonneg_left hnum hden hden_le
    calc
      compensatedLevyKernel c t x ≤ 2 * c / (Real.pi * |x| ^ 2) := hk
      _ ≤ (cauchyMajorantConstant c t / 2) / (|x| ^ 2) := hstep1
      _ ≤ cauchyMajorantConstant c t / (1 + x ^ 2) := hstep2
      _ = cauchyMajorantConstant c t * (1 + x ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]

/-- The compensated Lévy kernel is genuinely Lebesgue integrable on the real line. -/
theorem integrable_compensatedLevyKernel {c t : ℝ} (hc : 0 ≤ c) :
    Integrable (fun x : ℝ => compensatedLevyKernel c t x) := by
  have hg : Integrable (fun x : ℝ =>
      cauchyMajorantConstant c t * (1 + x ^ 2)⁻¹) :=
    Integrable.const_mul integrable_inv_one_add_sq (cauchyMajorantConstant c t)
  refine Integrable.mono' hg
    (aestronglyMeasurable_compensatedLevyKernel c t) ?_
  filter_upwards with x
  have hk0 : 0 ≤ compensatedLevyKernel c t x :=
    compensatedLevyKernel_nonneg (c := c) (t := t) (x := x) hc
  have hmaj := compensatedLevyKernel_le_cauchy (c := c) (t := t) (x := x) hc
  have hC : 0 ≤ cauchyMajorantConstant c t := by
    unfold cauchyMajorantConstant
    positivity
  have hinv : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hk0, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hC hinv)]
  exact hmaj

end GppContinuousSechLevyIntegrable

#print axioms GppContinuousSechLevyIntegrable.compensatedLevyKernel_le_cauchy
#print axioms GppContinuousSechLevyIntegrable.integrable_compensatedLevyKernel
