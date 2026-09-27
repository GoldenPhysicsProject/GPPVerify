import GppVerify.CelestialHolography.RaisedBoxStripIntegralBridge
import GppVerify.CelestialHolography.RaisedBoxInnerDCT
import GppVerify.CelestialHolography.RaisedBoxRealMajorantSliceIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Raised-box middle-coordinate measurability and dominated convergence

The measurable product-strip representation gives strong measurability of the
innermost integral as a function of `x2`.  On the physical middle simplex range,
the strip integral is exactly the variable-endpoint interval integral.  This file
transfers the product-measure certificate to the interval-integral function used
by the second dominated-convergence step.

It also packages the norm of that inner integral under the same one-channel
majorant used in the certified inner DCT and then performs the middle-coordinate
DCT.  For fixed `x1 > 0`, the explicit slice majorant is bounded by a constant,
so no additional endpoint-singular integrability theorem is needed at this stage.
-/

namespace GppRaisedBoxMiddleMeasurability

open Filter Set MeasureTheory
open scoped Interval Topology
open GppRaisedBoxConcreteMoment
open GppRaisedBoxStripIntegralBridge
open GppRaisedBoxRealMajorantSlice
open GppRaisedBoxRealMajorantSliceIntegral

/-- On the physical middle simplex interval, the variable-endpoint innermost
raised-box integral is a.e. strongly measurable in `x2`.  This is the exact
measurability hypothesis needed by the middle dominated-convergence theorem. -/
theorem intervalInnerIntegral_aestronglyMeasurable
    {ε S T x1 : ℝ} (hx1 : x1 ≤ 1) :
    AEStronglyMeasurable
      (fun x2 : ℝ =>
        ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
          integrand ε S T x1 x2 x3)
      (volume.restrict (Set.uIoc (0 : ℝ) (1 - x1))) := by
  have hstrip :
      AEStronglyMeasurable
        (fun x2 : ℝ =>
          ∫ x3 : ℝ,
            ((innerSimplexStrip x1).indicator
              (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2)) (x2, x3))
        (volume.restrict (Set.uIoc (0 : ℝ) (1 - x1))) :=
    (stripInnerIntegral_stronglyMeasurable ε S T x1).aestronglyMeasurable.restrict
  apply hstrip.congr
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x2 hx2
  rw [Set.uIoc_of_le (by linarith : (0 : ℝ) ≤ 1 - x1)] at hx2
  exact stripInnerIntegral_eq_intervalIntegral ε S T x1 x2 ⟨hx2.1.le, hx2.2⟩

/-- The norm of the variable-endpoint inner integral is bounded by the integral
of the certified one-channel majorant.  Unlike the pointwise inner DCT, this
statement keeps `x2` free and is therefore the exact domination interface for
the next (middle-coordinate) dominated-convergence step. -/
theorem intervalInnerIntegral_norm_le_integratedMajorant
    {δ ε S T x1 x2 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2) (hx12 : x1 + x2 ≤ 1) :
    ‖∫ x3 in (0 : ℝ)..(1 - x1 - x2),
        integrand ε S T x1 x2 x3‖ ≤
      ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
        (1 + (S * x1 * x3) ^ (-δ : ℝ)) := by
  have hL : 0 ≤ 1 - x1 - x2 := by linarith
  have hMajInt : IntervalIntegrable
      (fun x3 : ℝ => 1 + (S * x1 * x3) ^ (-δ : ℝ))
      volume 0 (1 - x1 - x2) := by
    exact intervalIntegrable_const.add
      (channel_inner_intervalIntegrable hδ1 hS.le hx1.le hL)
  have hAE : ∀ᵐ x3 : ℝ ∂volume.restrict (Set.uIoc (0 : ℝ) (1 - x1 - x2)),
      ‖integrand ε S T x1 x2 x3‖ ≤ 1 + (S * x1 * x3) ^ (-δ : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with x3 hx3mem
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
  have hAbs := intervalIntegral.norm_integral_le_of_norm_le hAE hMajInt
  have hMajNonneg : 0 ≤
      ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
        (1 + (S * x1 * x3) ^ (-δ : ℝ)) := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hL
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x3 hx3mem
    have hx3 : 0 ≤ x3 := hx3mem.1
    have hprod : 0 ≤ S * x1 * x3 := by
      exact mul_nonneg (mul_nonneg hS.le hx1.le) hx3
    exact add_nonneg zero_le_one (Real.rpow_nonneg hprod _)
  simpa [abs_of_nonneg hMajNonneg] using hAbs

/-- Explicit form of the previous norm bound after evaluating the singular
endpoint integral.  This is the middle-DCT majorant before integrating in `x2`.
-/
theorem intervalInnerIntegral_norm_le_explicitMajorant
    {δ ε S T x1 x2 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2) (hx12 : x1 + x2 ≤ 1) :
    ‖∫ x3 in (0 : ℝ)..(1 - x1 - x2),
        integrand ε S T x1 x2 x3‖ ≤
      (1 - x1 - x2) +
        (S * x1) ^ (-δ : ℝ) *
          ((1 - x1 - x2) ^ (1 - δ : ℝ) / (1 - δ)) := by
  have hL : 0 ≤ 1 - x1 - x2 := by linarith
  calc
    ‖∫ x3 in (0 : ℝ)..(1 - x1 - x2),
        integrand ε S T x1 x2 x3‖ ≤
        ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
          (1 + (S * x1 * x3) ^ (-δ : ℝ)) :=
      intervalInnerIntegral_norm_le_integratedMajorant
        hδ0 hδ1 hε0 hεδ hS hT hx1 hx2 hx12
    _ = (1 - x1 - x2) +
        (S * x1) ^ (-δ : ℝ) *
          ((1 - x1 - x2) ^ (1 - δ : ℝ) / (1 - δ)) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (channel_inner_intervalIntegrable hδ1 hS.le hx1.le hL)]
      rw [integral_channel_zero_to hδ1 hS.le hx1.le hL]
      simp

/-- For fixed `x1` in the strict simplex interior, the explicit middle majorant
is bounded by an `x2`-independent constant.  This removes all middle-coordinate
integrability bookkeeping from the second DCT; the only singular dependence is
in `x1`, which is handled by the outer layer. -/
theorem intervalInnerIntegral_norm_le_middleConstant
    {δ ε S T x1 x2 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2) (hx12 : x1 + x2 ≤ 1) :
    ‖∫ x3 in (0 : ℝ)..(1 - x1 - x2),
        integrand ε S T x1 x2 x3‖ ≤
      1 + (S * x1) ^ (-δ : ℝ) / (1 - δ) := by
  have hL0 : 0 ≤ 1 - x1 - x2 := by linarith
  have hL1 : 1 - x1 - x2 ≤ 1 := by linarith
  have hexp0 : 0 ≤ 1 - δ := by linarith
  have hrpow : (1 - x1 - x2) ^ (1 - δ : ℝ) ≤ 1 := by
    exact Real.rpow_le_one hL0 hL1 hexp0
  have hcoeff : 0 ≤ (S * x1) ^ (-δ : ℝ) :=
    Real.rpow_nonneg (mul_nonneg hS.le hx1.le) _
  have hden : 0 < 1 - δ := by linarith
  have hbase := intervalInnerIntegral_norm_le_explicitMajorant
    hδ0 hδ1 hε0 hεδ hS hT hx1 hx2 hx12
  calc
    ‖∫ x3 in (0 : ℝ)..(1 - x1 - x2),
        integrand ε S T x1 x2 x3‖ ≤
      (1 - x1 - x2) +
        (S * x1) ^ (-δ : ℝ) *
          ((1 - x1 - x2) ^ (1 - δ : ℝ) / (1 - δ)) := hbase
    _ ≤ 1 + (S * x1) ^ (-δ : ℝ) * (1 / (1 - δ)) := by
      gcongr
    _ = 1 + (S * x1) ^ (-δ : ℝ) / (1 - δ) := by
      simp [div_eq_mul_inv]

/-- Second dominated-convergence step for the raised scalar box.  For a fixed
strict `x1` slice, regulator removal commutes with the `x2` integration. -/
theorem middle_interval_tendsto_inner_one
    {δ S T x1 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx1lt : x1 < 1) :
    Tendsto
      (fun ε : ℝ =>
        ∫ x2 in (0 : ℝ)..(1 - x1),
          ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
            integrand ε S T x1 x2 x3)
      (𝓝[Set.Icc 0 δ] 0)
      (nhds
        (∫ x2 in (0 : ℝ)..(1 - x1),
          ∫ _x3 in (0 : ℝ)..(1 - x1 - x2), (1 : ℝ))) := by
  have hL : 0 < 1 - x1 := by linarith
  have hMeas :
      ∀ᶠ ε : ℝ in 𝓝[Set.Icc 0 δ] 0,
        AEStronglyMeasurable
          (fun x2 : ℝ =>
            ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
              integrand ε S T x1 x2 x3)
          (volume.restrict (Set.uIoc (0 : ℝ) (1 - x1))) := by
    filter_upwards with ε
    exact intervalInnerIntegral_aestronglyMeasurable hx1lt.le
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _x2 : ℝ => 1 + (S * x1) ^ (-δ : ℝ) / (1 - δ))
  · exact hMeas
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Eventually.of_forall ?_
    intro x2
    intro hx2mem
    rw [Set.uIoc_of_le hL.le] at hx2mem
    have hx2hi : x2 ≤ 1 - x1 := hx2mem.2
    have hx12 : x1 + x2 ≤ 1 := by linarith
    exact intervalInnerIntegral_norm_le_middleConstant
      hδ0 hδ1 hε.1 hε.2 hS hT hx1 hx2mem.1.le hx12
  · exact intervalIntegrable_const
  · filter_upwards [] with x2
    intro hx2mem
    rw [Set.uIoc_of_le hL.le] at hx2mem
    have hx2hi : x2 ≤ 1 - x1 := hx2mem.2
    have hx12 : x1 + x2 ≤ 1 := by linarith
    exact GppRaisedBoxInnerDCT.inner_interval_tendsto_one
      hδ0 hδ1 hS hT hx1 hx2mem.1 hx12

end GppRaisedBoxMiddleMeasurability

#print axioms GppRaisedBoxMiddleMeasurability.intervalInnerIntegral_aestronglyMeasurable
#print axioms GppRaisedBoxMiddleMeasurability.intervalInnerIntegral_norm_le_integratedMajorant
#print axioms GppRaisedBoxMiddleMeasurability.intervalInnerIntegral_norm_le_explicitMajorant
#print axioms GppRaisedBoxMiddleMeasurability.intervalInnerIntegral_norm_le_middleConstant
#print axioms GppRaisedBoxMiddleMeasurability.middle_interval_tendsto_inner_one