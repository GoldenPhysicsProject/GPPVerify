import GppVerify.CelestialHolography.SechConvolutionClosedForm
import GppVerify.CelestialHolography.SechConvolutionWienerHopf
import GppVerify.CelestialHolography.WienerHopfWeightExtension
import GppVerify.CelestialHolography.SechConvolutionEndpoints
import GppVerify.RiemannHypothesis.SechSquaredIntegral
import Mathlib.Tactic

/-!
# Zero-shift sech convolution

This file closes the removable `lambda = 0` case left out by the nonzero
closed-form theorem.  The primitive is

  `x ↦ tanh(pi*x)/pi`,

whose derivative is `1/cosh(pi*x)^2`.  The derivative of `tanh` is imported from
the project proof in `SechSquaredIntegral`, where it is derived from the
`sinh/cosh` quotient rule because pinned Mathlib does not expose it directly.
-/

namespace GppSechConvolutionZeroShift

open Filter MeasureTheory
open GppSechConvolutionClosedForm
open GppSechConvolutionWienerHopf
open GppWienerHopfWeightExtension

noncomputable def scaledTanh (x : ℝ) : ℝ := Real.tanh (Real.pi * x) / Real.pi

/-- Exponential form used to read off the endpoint of `tanh`. -/
theorem tanh_eq_exp_neg_two (u : ℝ) :
    Real.tanh u =
      (1 - Real.exp (-(2 * u))) / (1 + Real.exp (-(2 * u))) := by
  have hsplit : Real.exp (-u) = Real.exp u * Real.exp (-(2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, hsplit]
  have hd : Real.exp u + Real.exp u * Real.exp (-(2 * u)) ≠ 0 := by positivity
  field_simp
  ring

/-- `tanh x -> 1` at the right endpoint. -/
theorem tendsto_tanh_atTop :
    Tendsto Real.tanh atTop (nhds 1) := by
  rw [tendsto_congr tanh_eq_exp_neg_two]
  have h2u : Tendsto (fun u : ℝ => 2 * u) atTop atTop :=
    Tendsto.const_mul_atTop two_pos tendsto_id
  have hexp : Tendsto (fun u : ℝ => Real.exp (-(2 * u))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h2u
  have hnum : Tendsto (fun u : ℝ => 1 - Real.exp (-(2 * u))) atTop (nhds 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub hexp
    simpa using h
  have hden : Tendsto (fun u : ℝ => 1 + Real.exp (-(2 * u))) atTop (nhds 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).add hexp
    simpa using h
  have h := hnum.div hden one_ne_zero
  simpa using h

/-- `tanh x -> -1` at the left endpoint, by oddness. -/
theorem tendsto_tanh_atBot :
    Tendsto Real.tanh atBot (nhds (-1)) := by
  have hcomp := tendsto_tanh_atTop.comp tendsto_neg_atBot_atTop
  have hneg : Tendsto (fun x : ℝ => -Real.tanh (-x)) atBot (nhds (-1)) := by
    simpa using hcomp.neg
  exact hneg.congr' (Filter.Eventually.of_forall fun x => by simp)

/-- The scaled primitive differentiates to the zero-shift convolution kernel. -/
theorem hasDerivAt_scaledTanh (x : ℝ) :
    HasDerivAt scaledTanh (1 / Real.cosh (Real.pi * x) ^ 2) x := by
  have hinner : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
    simpa using (hasDerivAt_id x).const_mul Real.pi
  have hcomp := HasDerivAt.scomp x
    (GppSechIntegral.hasDerivAt_tanh (Real.pi * x)) hinner
  have h := hcomp.div_const Real.pi
  simpa [scaledTanh, Function.comp_def, Real.pi_ne_zero] using h

/-- Right endpoint of the scaled primitive. -/
theorem scaledTanh_tendsto_atTop :
    Tendsto scaledTanh atTop (nhds (1 / Real.pi)) := by
  have hpi : Tendsto (fun x : ℝ => Real.pi * x) atTop atTop :=
    Tendsto.const_mul_atTop Real.pi_pos tendsto_id
  have ht : Tendsto (fun x : ℝ => Real.tanh (Real.pi * x)) atTop (nhds 1) :=
    tendsto_tanh_atTop.comp hpi
  have h := ht.div
    (tendsto_const_nhds (x := Real.pi) (f := (atTop : Filter ℝ))) Real.pi_ne_zero
  simpa [scaledTanh] using h

/-- Left endpoint of the scaled primitive. -/
theorem scaledTanh_tendsto_atBot :
    Tendsto scaledTanh atBot (nhds (-1 / Real.pi)) := by
  have hcomp := scaledTanh_tendsto_atTop.comp tendsto_neg_atBot_atTop
  have hneg : Tendsto (fun x : ℝ => -scaledTanh (-x)) atBot
      (nhds (-(1 / Real.pi))) := by
    simpa using hcomp.neg
  have heq : (fun x : ℝ => -scaledTanh (-x)) = scaledTanh := by
    funext x
    rw [scaledTanh, scaledTanh]
    rw [show Real.pi * (-x) = -(Real.pi * x) by ring, Real.tanh_neg]
    ring
  rw [← heq]
  simpa only [neg_div] using hneg

/-- The zero-shift kernel is integrable on the whole line. -/
theorem integrable_zero_shift_kernel :
    Integrable (fun x : ℝ => 1 / Real.cosh (Real.pi * x) ^ 2) := by
  have hnonneg : ∀ x : ℝ, 0 ≤ 1 / Real.cosh (Real.pi * x) ^ 2 := by
    intro x
    positivity
  have hright : IntegrableOn
      (fun x : ℝ => 1 / Real.cosh (Real.pi * x) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg'
      (fun x _ => hasDerivAt_scaledTanh x)
      (fun x _ => hnonneg x)
      scaledTanh_tendsto_atTop
  have hreflect : IntegrableOn
      (fun x : ℝ => 1 / Real.cosh (Real.pi * (-x)) ^ 2) (Set.Ioi 0) := by
    simpa using hright
  rw [← integrableOn_univ, ← @Set.Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hright⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa [Function.comp_def] using hreflect

/-- **Zero-shift normalization**:
`∫_R sech^2(pi*x) dx = 2/pi`. -/
theorem integral_zero_shift_kernel_eq_two_div_pi :
    (∫ x : ℝ, 1 / Real.cosh (Real.pi * x) ^ 2) = 2 / Real.pi := by
  have h := integral_of_hasDerivAt_of_tendsto
    (fun x => hasDerivAt_scaledTanh x)
    integrable_zero_shift_kernel
    scaledTanh_tendsto_atBot
    scaledTanh_tendsto_atTop
  convert h using 1 <;> ring

/-- At `lambda = 0`, the shifted kernel is exactly the zero-shift kernel. -/
theorem integral_sech_convolution_zero :
    (∫ x : ℝ,
      1 / (Real.cosh (Real.pi * x) *
        Real.cosh (Real.pi * ((0 : ℝ) - x)))) = 2 / Real.pi := by
  convert integral_zero_shift_kernel_eq_two_div_pi using 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [show Real.pi * ((0 : ℝ) - x) = -(Real.pi * x) by ring,
    Real.cosh_neg, pow_two]

/-- **All-real Wiener-Hopf normalization.**  The exact sech self-convolution is
`(2/pi) * extendedWienerHopfWeight lambda`, including the removable origin. -/
theorem integral_sech_convolution_eq_extended_weight (lam : ℝ) :
    (∫ x : ℝ,
      1 / (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x)))) =
      (2 / Real.pi) * extendedWienerHopfWeight lam := by
  by_cases hlam : lam = 0
  · subst lam
    rw [integral_sech_convolution_zero, extendedWienerHopfWeight_zero]
    ring
  · rw [GppSechConvolutionWienerHopf.integral_sech_convolution_eq_wienerHopfWeight hlam,
      extendedWienerHopfWeight_eq hlam]

end GppSechConvolutionZeroShift

#print axioms GppSechConvolutionZeroShift.integral_zero_shift_kernel_eq_two_div_pi
#print axioms GppSechConvolutionZeroShift.integral_sech_convolution_eq_extended_weight
