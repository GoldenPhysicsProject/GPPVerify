import GppVerify.CelestialHolography.RaisedBoxOuterFiberBridge
import GppVerify.CelestialHolography.RaisedBoxRealMajorantSlice
import GppVerify.CelestialHolography.RaisedBoxStripIntegralBridge
import Mathlib.Tactic

/-!
# Raised-box outer section integrability

This file supplies the analytic section-integrability layer for the final
product-integrability certificate. For every physical `x2` slice at fixed
interior `x1`, the innermost raised-box integrand is interval-integrable by the
certified one-channel endpoint majorant. Extending that slice by zero off its
affine interval therefore gives an integrable whole-line section.
-/

namespace GppRaisedBoxOuterSectionIntegrability

open MeasureTheory
open scoped Interval
open GppRaisedBoxConcreteMoment
open GppRaisedBoxRealMajorantSlice
open GppRaisedBoxStripIntegralBridge

/-- The concrete raised-box integrand is interval-integrable on every physical
innermost affine slice whenever the regulator lies in `0 ≤ ε ≤ δ < 1`. -/
theorem integrand_inner_intervalIntegrable
    {δ ε S T x1 x2 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2) (hx12 : x1 + x2 ≤ 1) :
    IntervalIntegrable
      (fun x3 : ℝ => integrand ε S T x1 x2 x3)
      volume 0 (1 - x1 - x2) := by
  have hL : 0 ≤ 1 - x1 - x2 := by linarith
  have hMajInt : IntervalIntegrable
      (fun x3 : ℝ => 1 + (S * x1 * x3) ^ (-δ : ℝ))
      volume 0 (1 - x1 - x2) := by
    exact intervalIntegrable_const.add
      (channel_inner_intervalIntegrable hδ1 hS.le hx1.le hL)
  apply hMajInt.mono_fun'
  · exact (integrand_measurable_x3 ε S T x1 x2).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x3 hx3mem
    rw [Set.uIoc_of_le hL] at hx3mem
    have hx3 : 0 < x3 := hx3mem.1
    have hx3le : x3 ≤ 1 - x1 - x2 := hx3mem.2
    have hxsum : x1 + x2 + x3 ≤ 1 := by linarith
    have hslack : 0 ≤ 1 - x1 - x2 - x3 := by linarith
    have hQ : 0 ≤ Q S T x1 x2 x3 := by
      unfold Q
      positivity
    have hnonneg : 0 ≤ integrand ε S T x1 x2 x3 := by
      unfold integrand
      exact Real.rpow_nonneg hQ _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact integrand_le_one_channel_majorant
      hS hT hx1 hx2 hx3 hxsum hε0 hεδ hδ0

/-- The zero extension of a physical `x3` slice of the measurable inner strip
is integrable on the whole real line. -/
theorem strip_section_integrable
    {δ ε S T x1 x2 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2) (hx12 : x1 + x2 ≤ 1) :
    Integrable
      (fun x3 : ℝ =>
        ((innerSimplexStrip x1).indicator
          (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2)) (x2, x3)) := by
  have hL : 0 ≤ 1 - x1 - x2 := by linarith
  have hInterval := integrand_inner_intervalIntegrable
    hδ0 hδ1 hε0 hεδ hS hT hx1 hx2 hx12
  have hOn : IntegrableOn
      (fun x3 : ℝ => integrand ε S T x1 x2 x3)
      (Set.Icc (0 : ℝ) (1 - x1 - x2)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hL).mp hInterval
  have hIndicator : Integrable
      ((Set.Icc (0 : ℝ) (1 - x1 - x2)).indicator
        (fun x3 : ℝ => integrand ε S T x1 x2 x3)) :=
    hOn.integrable_indicator measurableSet_Icc
  simpa only [stripIntegrand_section_eq_Icc_indicator] using hIndicator

/-- On a physical slice, nonnegativity identifies the integral of the norm of
the zero-extended strip section with the original affine interval integral.
This is the quantity required by the second conjunct of `integrable_prod_iff`. -/
theorem strip_section_norm_integral_eq_intervalIntegral
    {ε S T x1 x2 : ℝ}
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2) (hx12 : x1 + x2 ≤ 1) :
    (∫ x3 : ℝ,
      ‖((innerSimplexStrip x1).indicator
        (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2)) (x2, x3)‖) =
      ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
        integrand ε S T x1 x2 x3 := by
  have hx2mem : x2 ∈ Set.Icc (0 : ℝ) (1 - x1) := by
    constructor <;> linarith
  calc
    (∫ x3 : ℝ,
      ‖((innerSimplexStrip x1).indicator
        (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2)) (x2, x3)‖) =
      ∫ x3 : ℝ,
        (Set.Icc (0 : ℝ) (1 - x1 - x2)).indicator
          (fun y : ℝ => integrand ε S T x1 x2 y) x3 := by
      apply integral_congr_ae
      filter_upwards [] with x3
      rw [stripIntegrand_section_eq_Icc_indicator]
      by_cases hx3 : x3 ∈ Set.Icc (0 : ℝ) (1 - x1 - x2)
      · rw [Set.indicator_of_mem hx3]
        have hx30 : 0 ≤ x3 := hx3.1
        have hx3hi : x3 ≤ 1 - x1 - x2 := hx3.2
        have hslack : 0 ≤ 1 - x1 - x2 - x3 := by linarith
        have hQ : 0 ≤ Q S T x1 x2 x3 := by
          unfold Q
          positivity
        have hnonneg : 0 ≤ integrand ε S T x1 x2 x3 := by
          unfold integrand
          exact Real.rpow_nonneg hQ _
        simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      · simp [Set.indicator_of_not_mem hx3]
    _ = ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
        integrand ε S T x1 x2 x3 :=
      IccIndicatorIntegral_eq_intervalIntegral ε S T x1 x2 hx2mem

end GppRaisedBoxOuterSectionIntegrability

#print axioms GppRaisedBoxOuterSectionIntegrability.integrand_inner_intervalIntegrable
#print axioms GppRaisedBoxOuterSectionIntegrability.strip_section_integrable
#print axioms GppRaisedBoxOuterSectionIntegrability.strip_section_norm_integral_eq_intervalIntegral
