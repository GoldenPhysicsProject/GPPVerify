import GppVerify.CelestialHolography.ContinuousSechLevyFrequencyDerivativeMajorant
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Frequency differentiability of the continuous sech Lévy kernel

For fixed spatial coordinate `x`, the compensated kernel

  K_c(t,x) = (1 - cos(t x)) nu_c(x)

is differentiable in the frequency parameter `t`, with exact derivative

  D_c(t,x) = x sin(t x) nu_c(x).

The parameter-uniform Cauchy majorant from
`ContinuousSechLevyFrequencyDerivativeMajorant` also implies that, for every
fixed frequency, the derivative kernel is genuinely Lebesgue integrable in `x`.
Combining these facts with Mathlib's dominated parametric-integral theorem gives
the actual differentiation-under-the-integral identity.
-/

namespace GppContinuousSechLevyFrequencyDifferentiability

open MeasureTheory
open GppContinuousSechLevyKernel
open GppContinuousSechLevyMeasurability
open GppContinuousSechLevyIntegrable
open GppContinuousSechLevyFrequencyDerivative
open GppContinuousSechLevyFrequencyDerivativeMajorant

/-- For every fixed spatial coordinate, the compensated Lévy kernel has the
expected frequency derivative.  No positivity or integrability assumption is
needed for this pointwise statement. -/
theorem hasDerivAt_compensatedLevyKernel_frequency (c x t : ℝ) :
    HasDerivAt (fun u : ℝ => compensatedLevyKernel c u x)
      (frequencyDerivativeKernel c t x) t := by
  unfold compensatedLevyKernel frequencyDerivativeKernel
  have hlin : HasDerivAt (fun u : ℝ => u * x) x t := by
    simpa using (hasDerivAt_id t).mul_const x
  have hcos : HasDerivAt (fun u : ℝ => Real.cos (u * x))
      (-Real.sin (t * x) * x) t :=
    (Real.hasDerivAt_cos (t * x)).comp t hlin
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  have hsub : HasDerivAt (fun u : ℝ => 1 - Real.cos (u * x))
      (Real.sin (t * x) * x) t := by
    convert hone.sub hcos using 1 <;> ring
  convert hsub.mul_const (levyDensity c x) using 1 <;> ring

/-- For fixed chamber parameter and frequency, the derivative kernel is Borel measurable
as a function of the spatial variable. -/
theorem measurable_frequencyDerivativeKernel (c t : ℝ) :
    Measurable (fun x : ℝ => frequencyDerivativeKernel c t x) := by
  unfold frequencyDerivativeKernel levyDensity
  fun_prop

/-- Hence the fixed-frequency derivative kernel is strongly measurable. -/
theorem aestronglyMeasurable_frequencyDerivativeKernel (c t : ℝ) :
    AEStronglyMeasurable (fun x : ℝ => frequencyDerivativeKernel c t x) :=
  (measurable_frequencyDerivativeKernel c t).aestronglyMeasurable

/-- For every nonnegative chamber parameter and every fixed frequency, the derivative
kernel is Lebesgue integrable on the real line.  The proof takes the compact frequency
window `T = |t|` in the certified Cauchy majorant. -/
theorem integrable_frequencyDerivativeKernel {c t : ℝ} (hc : 0 ≤ c) :
    Integrable (fun x : ℝ => frequencyDerivativeKernel c t x) := by
  let T : ℝ := |t|
  have hg : Integrable (fun x : ℝ =>
      frequencyDerivativeCauchyConstant c T * (1 + x ^ 2)⁻¹) :=
    integrable_frequencyDerivativeCauchyMajorant c T
  refine Integrable.mono' hg
    (aestronglyMeasurable_frequencyDerivativeKernel c t) ?_
  filter_upwards with x
  have hmaj := abs_frequencyDerivativeKernel_le_cauchy
    (c := c) (T := T) (t := t) (x := x) hc (le_refl |t|)
  have hT : 0 ≤ T := abs_nonneg t
  have hgap : 0 < 1 - Real.exp (-(2 * Real.pi)) := by
    have : Real.exp (-(2 * Real.pi)) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    linarith
  have hC : 0 ≤ frequencyDerivativeCauchyConstant c T := by
    unfold frequencyDerivativeCauchyConstant
    positivity
  have hinv : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hC hinv)]
  exact hmaj

/-- The spatial integral of the compensated Lévy kernel is differentiable in frequency,
with derivative equal to the spatial integral of the pointwise derivative kernel.

The domination is genuinely local-uniform: on the unit frequency ball around `t`, the
fixed Cauchy majorant uses the window `T = |t| + 1`. -/
theorem hasDerivAt_integral_compensatedLevyKernel_frequency {c t : ℝ} (hc : 0 ≤ c) :
    HasDerivAt
      (fun u : ℝ => ∫ x : ℝ, compensatedLevyKernel c u x)
      (∫ x : ℝ, frequencyDerivativeKernel c t x) t := by
  let T : ℝ := |t| + 1
  let bound : ℝ → ℝ := fun x =>
    frequencyDerivativeCauchyConstant c T * (1 + x ^ 2)⁻¹
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  have hFmeas : ∀ᶠ u in 𝓝 t,
      AEStronglyMeasurable (fun x : ℝ => compensatedLevyKernel c u x) := by
    filter_upwards with u
    exact aestronglyMeasurable_compensatedLevyKernel c u
  have hFint : Integrable (fun x : ℝ => compensatedLevyKernel c t x) :=
    integrable_compensatedLevyKernel hc
  have hF'meas : AEStronglyMeasurable
      (fun x : ℝ => frequencyDerivativeKernel c t x) :=
    aestronglyMeasurable_frequencyDerivativeKernel c t
  have hboundInt : Integrable bound := by
    dsimp [bound]
    exact integrable_frequencyDerivativeCauchyMajorant c T
  have hbound : ∀ᵐ x : ℝ,
      ∀ u ∈ Metric.ball t (1 : ℝ),
        ‖frequencyDerivativeKernel c u x‖ ≤ bound x := by
    filter_upwards with x
    intro u hu
    have hut : |u| ≤ T := by
      have hudist : |u - t| < 1 := by
        simpa [Real.dist_eq] using hu
      have huabs : |u| ≤ |u - t| + |t| := by
        calc
          |u| = |(u - t) + t| := by ring_nf
          _ ≤ |u - t| + |t| := abs_add _ _
      dsimp [T]
      linarith
    have hmaj := abs_frequencyDerivativeKernel_le_cauchy
      (c := c) (T := T) (t := u) (x := x) hc hut
    simpa [bound, Real.norm_eq_abs] using hmaj
  have hdiff : ∀ᵐ x : ℝ,
      ∀ u ∈ Metric.ball t (1 : ℝ),
        HasDerivAt (fun v : ℝ => compensatedLevyKernel c v x)
          (frequencyDerivativeKernel c u x) u := by
    filter_upwards with x
    intro u hu
    exact hasDerivAt_compensatedLevyKernel_frequency c x u
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u : ℝ => fun x : ℝ => compensatedLevyKernel c u x)
    (F' := fun u : ℝ => fun x : ℝ => frequencyDerivativeKernel c u x)
    (x₀ := t) (bound := bound) (μ := volume) (ε := (1 : ℝ))
    (by norm_num) hFmeas hFint hF'meas hbound hboundInt hdiff).2

end GppContinuousSechLevyFrequencyDifferentiability

#print axioms GppContinuousSechLevyFrequencyDifferentiability.hasDerivAt_compensatedLevyKernel_frequency
#print axioms GppContinuousSechLevyFrequencyDifferentiability.measurable_frequencyDerivativeKernel
#print axioms GppContinuousSechLevyFrequencyDifferentiability.integrable_frequencyDerivativeKernel
#print axioms GppContinuousSechLevyFrequencyDifferentiability.hasDerivAt_integral_compensatedLevyKernel_frequency
