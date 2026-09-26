import GppVerify.CelestialHolography.SechConvolutionPrimitive
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Endpoint limits and finite-interval FTC for the shifted sech convolution

This file converts the quantitative remainder bounds from
`SechConvolutionPrimitive` into genuine endpoint limits. Both endpoints are
obtained without an improper-integral assumption: the right endpoint follows
from the exponentially small remainders, and the left endpoint follows by the
exact reflection `x ↦ lambda - x`.

It also closes the finite-interval calculus layer and the scaled whole-line
improper integral. The unscaled self-convolution follows by extracting the fixed
factor `pi*sinh(pi*lambda)` away from `lambda = 0`.
-/

namespace GppSechConvolutionEndpoints

open Filter MeasureTheory
open GppSechConvolutionPrimitive
open scoped Interval

/-- The first log-cosh remainder vanishes as `x → +∞`. -/
theorem logCoshRemainder_pi_mul_tendsto_atTop :
    Tendsto (fun x : ℝ => logCoshRemainder (Real.pi * x)) atTop (nhds 0) := by
  have hlin : Tendsto (fun x : ℝ => (2 * Real.pi) * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  have hupper :
      Tendsto (fun x : ℝ => Real.exp (-((2 * Real.pi) * x))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro x
    exact logCoshRemainder_nonneg (Real.pi * x)
  · intro x
    calc
      logCoshRemainder (Real.pi * x)
          ≤ Real.exp (-2 * |Real.pi * x|) := logCoshRemainder_le_exp _
      _ ≤ Real.exp (-((2 * Real.pi) * x)) := by
        apply Real.exp_le_exp.mpr
        have habs : Real.pi * x ≤ |Real.pi * x| := le_abs_self _
        linarith

/-- The reflected remainder also vanishes as `x → +∞`. -/
theorem logCoshRemainder_pi_shift_tendsto_atTop (lam : ℝ) :
    Tendsto (fun x : ℝ => logCoshRemainder (Real.pi * (lam - x))) atTop (nhds 0) := by
  have hlin0 : Tendsto (fun x : ℝ => (2 * Real.pi) * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  have hlin :
      Tendsto (fun x : ℝ => (2 * Real.pi) * x + (-(2 * Real.pi * lam))) atTop atTop :=
    tendsto_atTop_add_const_right _ _ hlin0
  have hupper0 :
      Tendsto
        (fun x : ℝ => Real.exp (-((2 * Real.pi) * x + (-(2 * Real.pi * lam)))))
        atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have hupper :
      Tendsto (fun x : ℝ => Real.exp (-((2 * Real.pi) * (x - lam))))
        atTop (nhds 0) := by
    simpa [mul_sub] using hupper0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro x
    exact logCoshRemainder_nonneg (Real.pi * (lam - x))
  · intro x
    calc
      logCoshRemainder (Real.pi * (lam - x))
          ≤ Real.exp (-2 * |Real.pi * (lam - x)|) := logCoshRemainder_le_exp _
      _ ≤ Real.exp (-((2 * Real.pi) * (x - lam))) := by
        apply Real.exp_le_exp.mpr
        have habs0 : -(Real.pi * (lam - x)) ≤ |Real.pi * (lam - x)| := neg_le_abs _
        have habs : Real.pi * (x - lam) ≤ |Real.pi * (lam - x)| := by
          rw [show Real.pi * (x - lam) = -(Real.pi * (lam - x)) by ring]
          exact habs0
        linarith

/-- **Right endpoint of the log-cosh primitive.** -/
theorem logCoshDifference_tendsto_atTop (lam : ℝ) :
    Tendsto (logCoshDifference lam) atTop (nhds (Real.pi * lam)) := by
  have h1 := logCoshRemainder_pi_mul_tendsto_atTop
  have h2 := logCoshRemainder_pi_shift_tendsto_atTop lam
  have hrem :
      Tendsto
        (fun x : ℝ => logCoshRemainder (Real.pi * x) -
          logCoshRemainder (Real.pi * (lam - x))) atTop (nhds 0) := by
    simpa using h1.sub h2
  have heq :
      (fun x : ℝ => logCoshDifference lam x - Real.pi * lam) =ᶠ[atTop]
        (fun x : ℝ => logCoshRemainder (Real.pi * x) -
          logCoshRemainder (Real.pi * (lam - x))) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), eventually_ge_atTop lam] with x hx0 hxlam
    exact logCoshDifference_right_remainder hx0 hxlam
  have hzero :
      Tendsto (fun x : ℝ => logCoshDifference lam x - Real.pi * lam)
        atTop (nhds 0) :=
    hrem.congr' heq.symm
  have hadd := hzero.add_const (Real.pi * lam)
  simpa using hadd

/-- Exact reflection of the primitive about `x = lambda/2`. -/
theorem logCoshDifference_reflect (lam x : ℝ) :
    -logCoshDifference lam (lam - x) = logCoshDifference lam x := by
  simp [logCoshDifference]

/-- **Left endpoint of the log-cosh primitive.** -/
theorem logCoshDifference_tendsto_atBot (lam : ℝ) :
    Tendsto (logCoshDifference lam) atBot (nhds (-Real.pi * lam)) := by
  have hmap0 : Tendsto (fun x : ℝ => -x) atBot atTop := tendsto_neg_atBot_atTop
  have hmap1 : Tendsto (fun x : ℝ => -x + lam) atBot atTop :=
    tendsto_atTop_add_const_right _ lam hmap0
  have hmap : Tendsto (fun x : ℝ => lam - x) atBot atTop := by
    simpa [sub_eq_add_neg, add_comm] using hmap1
  have hright := (logCoshDifference_tendsto_atTop lam).comp hmap
  have hneg :
      Tendsto (fun x : ℝ => -logCoshDifference lam (lam - x))
        atBot (nhds (-Real.pi * lam)) := by
    convert hright.neg using 1 <;> ring
  exact hneg.congr' (Filter.Eventually.of_forall fun x => logCoshDifference_reflect lam x)

/-- The derivative kernel from `hasDerivAt_logCoshDifference` is continuous on
all of `ℝ`; both cosh factors are strictly positive. -/
theorem continuous_scaled_sech_kernel (lam : ℝ) :
    Continuous (fun x : ℝ =>
      Real.pi * Real.sinh (Real.pi * lam) /
        (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x)))) := by
  have hx : Continuous (fun x : ℝ => Real.pi * x) :=
    continuous_const.mul continuous_id
  have hshift : Continuous (fun x : ℝ => Real.pi * (lam - x)) :=
    continuous_const.mul (continuous_const.sub continuous_id)
  have hc1 : Continuous (fun x : ℝ => Real.cosh (Real.pi * x)) :=
    Real.continuous_cosh.comp hx
  have hc2 : Continuous (fun x : ℝ => Real.cosh (Real.pi * (lam - x))) :=
    Real.continuous_cosh.comp hshift
  have hden : Continuous (fun x : ℝ =>
      Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x))) := hc1.mul hc2
  have hne : ∀ x : ℝ,
      Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x)) ≠ 0 := by
    intro x
    exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  exact continuous_const.div hden hne

/-- **Finite-interval shifted sech convolution identity.**  Before any
improper-limit passage, the scaled kernel integrates exactly to the jump of the
log-cosh primitive. -/
theorem integral_scaled_sech_kernel_eq_logCoshDifference_sub
    (lam a b : ℝ) :
    (∫ x in a..b,
      Real.pi * Real.sinh (Real.pi * lam) /
        (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x)))) =
      logCoshDifference lam b - logCoshDifference lam a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact hasDerivAt_logCoshDifference lam x
  · exact (continuous_scaled_sech_kernel lam).intervalIntegrable a b

/-- Reflection through the origin preserves the scaled-kernel derivative after also
negating the primitive. This is the device used to turn the left improper tail into
Mathlib's right-half-line FTC theorem. -/
theorem hasDerivAt_neg_logCoshDifference_neg (lam x : ℝ) :
    HasDerivAt (fun y : ℝ => -logCoshDifference lam (-y))
      (Real.pi * Real.sinh (Real.pi * lam) /
        (Real.cosh (Real.pi * (-x)) * Real.cosh (Real.pi * (lam - (-x))))) x := by
  have hcomp := HasDerivAt.scomp x (hasDerivAt_logCoshDifference lam (-x)) (hasDerivAt_neg' x)
  simpa [Function.comp_def] using hcomp.neg

/-- The reflected primitive has the same `+∞` limit `pi*lambda` as the original
primitive. -/
theorem neg_logCoshDifference_neg_tendsto_atTop (lam : ℝ) :
    Tendsto (fun x : ℝ => -logCoshDifference lam (-x)) atTop (nhds (Real.pi * lam)) := by
  have h := (logCoshDifference_tendsto_atBot lam).comp tendsto_neg_atTop_atBot
  convert h.neg using 1 <;> ring

/-- The scaled shifted-sech kernel is integrable on the whole real line. The proof
uses its fixed sign and the finite endpoint limits of the primitive rather than an
independent exponential majorant. -/
theorem integrable_scaled_sech_kernel (lam : ℝ) :
    Integrable (fun x : ℝ =>
      Real.pi * Real.sinh (Real.pi * lam) /
        (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x)))) := by
  rcases lt_trichotomy lam 0 with hneg | rfl | hpos
  · have hsinh : Real.sinh (Real.pi * lam) < 0 :=
      Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg Real.pi_pos hneg)
    have hkernel_nonpos : ∀ x : ℝ,
        Real.pi * Real.sinh (Real.pi * lam) /
            (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x))) ≤ 0 := by
      intro x
      exact le_of_lt (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg Real.pi_pos hsinh)
        (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)))
    have hright : IntegrableOn (fun x : ℝ =>
        Real.pi * Real.sinh (Real.pi * lam) /
          (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x)))) (Set.Ioi 0) :=
      integrableOn_Ioi_deriv_of_nonpos'
        (fun x _ => hasDerivAt_logCoshDifference lam x)
        (fun x _ => hkernel_nonpos x)
        (logCoshDifference_tendsto_atTop lam)
    have hreflect : IntegrableOn (fun x : ℝ =>
        Real.pi * Real.sinh (Real.pi * lam) /
          (Real.cosh (Real.pi * (-x)) * Real.cosh (Real.pi * (lam - (-x))))) (Set.Ioi 0) :=
      integrableOn_Ioi_deriv_of_nonpos'
        (fun x _ => hasDerivAt_neg_logCoshDifference_neg lam x)
        (fun x _ => hkernel_nonpos (-x))
        (neg_logCoshDifference_neg_tendsto_atTop lam)
    rw [← integrableOn_univ, ← @Set.Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
      integrableOn_Ici_iff_integrableOn_Ioi]
    refine ⟨?_, hright⟩
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa [Function.comp_def] using hreflect
  · simp
  · have hsinh : 0 < Real.sinh (Real.pi * lam) :=
      Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hpos)
    have hkernel_nonneg : ∀ x : ℝ, 0 ≤
        Real.pi * Real.sinh (Real.pi * lam) /
            (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x))) := by
      intro x
      exact le_of_lt (div_pos (mul_pos Real.pi_pos hsinh)
        (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)))
    have hright : IntegrableOn (fun x : ℝ =>
        Real.pi * Real.sinh (Real.pi * lam) /
          (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x)))) (Set.Ioi 0) :=
      integrableOn_Ioi_deriv_of_nonneg'
        (fun x _ => hasDerivAt_logCoshDifference lam x)
        (fun x _ => hkernel_nonneg x)
        (logCoshDifference_tendsto_atTop lam)
    have hreflect : IntegrableOn (fun x : ℝ =>
        Real.pi * Real.sinh (Real.pi * lam) /
          (Real.cosh (Real.pi * (-x)) * Real.cosh (Real.pi * (lam - (-x))))) (Set.Ioi 0) :=
      integrableOn_Ioi_deriv_of_nonneg'
        (fun x _ => hasDerivAt_neg_logCoshDifference_neg lam x)
        (fun x _ => hkernel_nonneg (-x))
        (neg_logCoshDifference_neg_tendsto_atTop lam)
    rw [← integrableOn_univ, ← @Set.Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
      integrableOn_Ici_iff_integrableOn_Ioi]
    refine ⟨?_, hright⟩
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa [Function.comp_def] using hreflect

/-- **Scaled whole-line shifted-sech convolution.** The improper integral is exactly
the endpoint jump of the certified primitive. -/
theorem integral_scaled_sech_kernel_eq_two_pi_mul (lam : ℝ) :
    (∫ x : ℝ,
      Real.pi * Real.sinh (Real.pi * lam) /
        (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x)))) =
      2 * Real.pi * lam := by
  have h := integral_of_hasDerivAt_of_tendsto
    (fun x => hasDerivAt_logCoshDifference lam x)
    (integrable_scaled_sech_kernel lam)
    (logCoshDifference_tendsto_atBot lam)
    (logCoshDifference_tendsto_atTop lam)
  convert h using 1 <;> ring

end GppSechConvolutionEndpoints

#print axioms GppSechConvolutionEndpoints.logCoshRemainder_pi_mul_tendsto_atTop
#print axioms GppSechConvolutionEndpoints.logCoshRemainder_pi_shift_tendsto_atTop
#print axioms GppSechConvolutionEndpoints.logCoshDifference_tendsto_atTop
#print axioms GppSechConvolutionEndpoints.logCoshDifference_tendsto_atBot
#print axioms GppSechConvolutionEndpoints.continuous_scaled_sech_kernel
#print axioms GppSechConvolutionEndpoints.integral_scaled_sech_kernel_eq_logCoshDifference_sub
#print axioms GppSechConvolutionEndpoints.hasDerivAt_neg_logCoshDifference_neg
#print axioms GppSechConvolutionEndpoints.integrable_scaled_sech_kernel
#print axioms GppSechConvolutionEndpoints.integral_scaled_sech_kernel_eq_two_pi_mul
