import GppVerify.CelestialHolography.RaisedBoxOuterNestedMeasurability
import GppVerify.CelestialHolography.RaisedBoxOuterNormBound
import GppVerify.CelestialHolography.RaisedBoxOuterDCTMajorant
import GppVerify.CelestialHolography.RaisedBoxConcreteVolumeClosure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Raised-box outer dominated-convergence closure

The inner and middle regulator limits, product/Fubini bridges, outer
measurability, and explicit integrable outer majorant are now all certified.
This file performs the final `x1` dominated-convergence step in the original
nested Feynman-parameter coordinates.

For `0 < δ < 1`, `S,T > 0`, and `ε -> 0` through `0 ≤ ε ≤ δ`, this closes

  simplexMoment ε S T -> simplexVolume = 1/6.

The module is also the direct changed-Lean certification target for the complete
raised-box dependency chain, including the concrete `1/6` normalization.
-/

namespace GppRaisedBoxOuterDCTClosure

open Filter Set MeasureTheory
open scoped Interval Topology
open GppRaisedBoxConcreteMoment
open GppRaisedBoxMiddleMeasurability
open GppRaisedBoxOuterNestedMeasurability
open GppRaisedBoxOuterNormBound
open GppRaisedBoxOuterDCTMajorant
open GppRaisedBoxConcreteVolumeClosure

/-- The interval-integral measure on `(0,1]` agrees with the restriction to the
strict interval `(0,1)` because Lebesgue measure has null singletons.  This is
the endpoint bookkeeping needed to reuse the strict-slice theorems in the final
outer DCT. -/
theorem restrict_uIoc_zero_one_eq_restrict_Ioo :
    volume.restrict (Set.uIoc (0 : ℝ) 1) =
      volume.restrict (Set.Ioo (0 : ℝ) 1) := by
  rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (Measure.restrict_congr_set
    (Ioo_ae_eq_Ioc : Set.Ioo (0 : ℝ) 1 =ᵐ[volume] Set.Ioc 0 1)).symm

/-- Final outer dominated-convergence theorem: the concrete raised-box simplex
moment tends to the zero-regulator affine simplex volume. -/
theorem simplexMoment_tendsto_simplexVolume
    {δ S T : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hS : 0 < S) (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ => simplexMoment ε S T)
      (𝓝[Set.Icc 0 δ] 0)
      (nhds simplexVolume) := by
  let F : ℝ → ℝ → ℝ := fun ε x1 =>
    ∫ x2 in (0 : ℝ)..(1 - x1),
      ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
        integrand ε S T x1 x2 x3
  let F0 : ℝ → ℝ := fun x1 =>
    ∫ x2 in (0 : ℝ)..(1 - x1),
      ∫ _x3 in (0 : ℝ)..(1 - x1 - x2), (1 : ℝ)
  let B : ℝ → ℝ := fun x1 =>
    1 + (S * x1) ^ (-δ : ℝ) / (1 - δ)
  have hμ := restrict_uIoc_zero_one_eq_restrict_Ioo
  have hMeas :
      ∀ᶠ ε : ℝ in 𝓝[Set.Icc 0 δ] 0,
        AEStronglyMeasurable (F ε)
          (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hμ]
    exact nestedInnerIntegral_aestronglyMeasurable_Ioo
      hδ0 hδ1 hε.1 hε.2 hS hT
  have hTend :
      Tendsto
        (fun ε : ℝ => ∫ x1 in (0 : ℝ)..1, F ε x1)
        (𝓝[Set.Icc 0 δ] 0)
        (nhds (∫ x1 in (0 : ℝ)..1, F0 x1)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := B)
    · exact hMeas
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards with x1
      intro hx1
      rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hx1
      by_cases hxone : x1 = 1
      · subst x1
        have hF1 : F ε 1 = 0 := by
          simp [F]
        rw [hF1]
        simp only [norm_zero, B, mul_one]
        have hpow : 0 ≤ S ^ (-δ : ℝ) :=
          (Real.rpow_pos_of_pos hS (-δ)).le
        have hden : 0 ≤ 1 - δ := (sub_pos.mpr hδ1).le
        exact add_nonneg zero_le_one (div_nonneg hpow hden)
      · exact nestedInnerIntegral_norm_le_outerMajorant
          hδ0 hδ1 hε.1 hε.2 hS hT hx1.1 (lt_of_le_of_ne hx1.2 hxone)
    · exact middleConstant_outer_intervalIntegrable hδ0 hδ1 hS
    · filter_upwards with x1
      intro hx1
      rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hx1
      by_cases hxone : x1 = 1
      · subst x1
        change Tendsto (fun ε : ℝ => F ε 1)
          (𝓝[Set.Icc 0 δ] 0) (nhds (F0 1))
        have hF1 : ∀ ε : ℝ, F ε 1 = 0 := by
          intro ε
          simp [F]
        have hF01 : F0 1 = 0 := by
          simp [F0]
        simpa only [hF1, hF01] using
          (tendsto_const_nhds :
            Tendsto (fun _ : ℝ => (0 : ℝ))
              (𝓝[Set.Icc 0 δ] 0) (nhds 0))
      · exact middle_interval_tendsto_inner_one
          hδ0 hδ1 hS hT hx1.1 (lt_of_le_of_ne hx1.2 hxone)
  simpa [F, F0, simplexMoment, simplexVolume] using hTend

/-- Concrete regulator closure of the raised scalar box simplex moment. -/
theorem simplexMoment_tendsto_one_sixth
    {δ S T : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hS : 0 < S) (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ => simplexMoment ε S T)
      (𝓝[Set.Icc 0 δ] 0)
      (nhds (1 / 6 : ℝ)) := by
  simpa [simplexVolume_eq_one_sixth] using
    simplexMoment_tendsto_simplexVolume hδ0 hδ1 hS hT

/-- Public scalar-box regulator endpoint.  This theorem intentionally repeats
the physical `1/6` target under a stable name so downstream cut/dispersion work
need not depend on the internal simplex-volume normalization theorem. -/
theorem scalarBox_regulator_tendsto_one_sixth
    {δ S T : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hS : 0 < S) (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ => simplexMoment ε S T)
      (𝓝[Set.Icc 0 δ] 0)
      (nhds (1 / 6 : ℝ)) :=
  simplexMoment_tendsto_one_sixth hδ0 hδ1 hS hT

end GppRaisedBoxOuterDCTClosure

#print axioms GppRaisedBoxOuterDCTClosure.restrict_uIoc_zero_one_eq_restrict_Ioo
#print axioms GppRaisedBoxOuterDCTClosure.simplexMoment_tendsto_simplexVolume
#print axioms GppRaisedBoxOuterDCTClosure.simplexMoment_tendsto_one_sixth
#print axioms GppRaisedBoxOuterDCTClosure.scalarBox_regulator_tendsto_one_sixth
