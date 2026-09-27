import GppVerify.CelestialHolography.RaisedBoxOuterSectionIntegrability
import GppVerify.CelestialHolography.RaisedBoxMiddleMeasurability
import GppVerify.CelestialHolography.RaisedBoxOuterFiberBridge
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Raised-box outer product integrability

The final Fubini bridge requires integrability of the fixed-`x1` two-dimensional
simplex section.  The nontrivial second conjunct of `integrable_prod_iff` is the
integrability in `x2` of the integral of the `x3`-section norm.

On the physical interval the certified norm-integral identity identifies that
quantity with the ordinary variable-endpoint inner integral.  The middle-DCT
majorant already bounds this inner integral by an `x2`-independent constant for
fixed strict `x1`, so no new singular estimate is required here.
-/

namespace GppRaisedBoxOuterProductIntegrability

open Filter Set MeasureTheory
open scoped Interval Topology
open GppRaisedBoxConcreteMoment
open GppRaisedBoxMiddleMeasurability
open GppRaisedBoxOuterSectionIntegrability
open GppRaisedBoxOuterFiberBridge
open GppRaisedBoxOuterMeasurability

/-- For fixed strict outer coordinate, the physical variable-endpoint inner
integral is interval-integrable in the middle coordinate. -/
theorem intervalInnerIntegral_intervalIntegrable
    {δ ε S T x1 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx1lt : x1 < 1) :
    IntervalIntegrable
      (fun x2 : ℝ =>
        ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
          integrand ε S T x1 x2 x3)
      volume 0 (1 - x1) := by
  have hL : 0 ≤ 1 - x1 := by linarith
  let C : ℝ := 1 + (S * x1) ^ (-δ : ℝ) / (1 - δ)
  apply (intervalIntegrable_const :
    IntervalIntegrable (fun _x2 : ℝ => C) volume 0 (1 - x1)).mono_fun'
  · exact intervalInnerIntegral_aestronglyMeasurable hx1lt.le
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x2 hx2
    rw [Set.uIoc_of_le hL] at hx2
    have hx2le : x2 ≤ 1 - x1 := hx2.2
    have hx12 : x1 + x2 ≤ 1 := by linarith
    exact intervalInnerIntegral_norm_le_middleConstant
      hδ0 hδ1 hε0 hεδ hS hT hx1 hx2.1.le hx12

/-- Zero-extending the physical middle integral outside its compact affine
interval gives a globally integrable function. -/
theorem IccIndicator_intervalInnerIntegral_integrable
    {δ ε S T x1 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx1lt : x1 < 1) :
    Integrable
      ((Set.Icc (0 : ℝ) (1 - x1)).indicator
        (fun x2 : ℝ =>
          ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
            integrand ε S T x1 x2 x3)) := by
  have hL : 0 ≤ 1 - x1 := by linarith
  have hInterval := intervalInnerIntegral_intervalIntegrable
    hδ0 hδ1 hε0 hεδ hS hT hx1 hx1lt
  have hOn : IntegrableOn
      (fun x2 : ℝ =>
        ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
          integrand ε S T x1 x2 x3)
      (Set.Icc (0 : ℝ) (1 - x1)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hL).mp hInterval
  exact hOn.integrable_indicator measurableSet_Icc

/-- For every strict physical outer coordinate, the complete two-dimensional
full-simplex fiber is Bochner integrable. -/
theorem fullSimplexFiber_integrable
    {δ ε S T x1 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx1lt : x1 < 1) :
    Integrable
      (fun p : ℝ × ℝ =>
        (fullSimplexSet.indicator
          (fun q : ℝ × (ℝ × ℝ) =>
            integrand ε S T q.1 q.2.1 q.2.2)) (x1, p)) := by
  let f : ℝ × ℝ → ℝ := fun p =>
    (fullSimplexSet.indicator
      (fun q : ℝ × (ℝ × ℝ) =>
        integrand ε S T q.1 q.2.1 q.2.2)) (x1, p)
  have hx1mem : x1 ∈ Set.Icc (0 : ℝ) 1 := ⟨hx1.le, hx1lt.le⟩
  have hMeas : Measurable f := by
    dsimp [f]
    exact (fullSimplexIntegrand_measurable ε S T).comp measurable_prodMk_left
  have hSections : ∀ᵐ x2 : ℝ, Integrable (fun x3 : ℝ => f (x2, x3)) := by
    filter_upwards [] with x2
    by_cases hx2 : x2 ∈ Set.Icc (0 : ℝ) (1 - x1)
    · have hx12 : x1 + x2 ≤ 1 := by linarith [hx2.2]
      have hStrip := strip_section_integrable
        hδ0 hδ1 hε0 hεδ hS hT hx1 hx2.1 hx12
      apply hStrip.congr
      filter_upwards [] with x3
      dsimp [f]
      rw [fullSimplexIndicator_section_factor ε S T hx1mem]
      simp [Set.indicator_of_mem hx2]
    · have hZero : Integrable (fun _x3 : ℝ => (0 : ℝ)) volume :=
        integrable_zero ℝ ℝ volume
      apply hZero.congr
      filter_upwards [] with x3
      dsimp [f]
      rw [fullSimplexIndicator_section_factor ε S T hx1mem]
      simp [Set.indicator_of_not_mem hx2]
  have hNormEq :
      (fun x2 : ℝ => ∫ x3 : ℝ, ‖f (x2, x3)‖) =
        (Set.Icc (0 : ℝ) (1 - x1)).indicator
          (fun x2 : ℝ =>
            ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
              integrand ε S T x1 x2 x3) := by
    funext x2
    by_cases hx2 : x2 ∈ Set.Icc (0 : ℝ) (1 - x1)
    · rw [Set.indicator_of_mem hx2]
      have hx12 : x1 + x2 ≤ 1 := by linarith [hx2.2]
      calc
        (∫ x3 : ℝ, ‖f (x2, x3)‖) =
            ∫ x3 : ℝ,
              ‖((innerSimplexStrip x1).indicator
                (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2)) (x2, x3)‖ := by
          apply integral_congr_ae
          filter_upwards [] with x3
          dsimp [f]
          rw [fullSimplexIndicator_section_factor ε S T hx1mem]
          simp [Set.indicator_of_mem hx2]
        _ = ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
              integrand ε S T x1 x2 x3 :=
          strip_section_norm_integral_eq_intervalIntegral
            hS hT hx1 hx2.1 hx12
    · rw [Set.indicator_of_not_mem hx2]
      have hfzero : ∀ x3 : ℝ, f (x2, x3) = 0 := by
        intro x3
        dsimp [f]
        rw [fullSimplexIndicator_section_factor ε S T hx1mem]
        simp [Set.indicator_of_not_mem hx2]
      simp_rw [hfzero]
      simp
  have hNormInt : Integrable (fun x2 : ℝ => ∫ x3 : ℝ, ‖f (x2, x3)‖) := by
    rw [hNormEq]
    exact IccIndicator_intervalInnerIntegral_integrable
      hδ0 hδ1 hε0 hεδ hS hT hx1 hx1lt
  have hProd : Integrable f (volume.prod volume) :=
    (integrable_prod_iff hMeas.aestronglyMeasurable).2 ⟨hSections, hNormInt⟩
  rw [← MeasureTheory.Measure.volume_eq_prod ℝ ℝ] at hProd
  exact hProd

end GppRaisedBoxOuterProductIntegrability

#print axioms GppRaisedBoxOuterProductIntegrability.intervalInnerIntegral_intervalIntegrable
#print axioms GppRaisedBoxOuterProductIntegrability.IccIndicator_intervalInnerIntegral_integrable
#print axioms GppRaisedBoxOuterProductIntegrability.fullSimplexFiber_integrable
