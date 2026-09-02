import GppVerify.CelestialHolography.RaisedBoxMiddleDCTPrep
import GppVerify.CelestialHolography.RaisedBoxMiddleMeasurability
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Raised-box middle dominated-convergence layer

This module completes the `x2` dominated-convergence argument after the inner
`x3` DCT.  The variable-endpoint slice is made measurable by the jointly
measurable whole-line indicator model from `RaisedBoxMiddleMeasurability`;
domination, pointwise convergence, majorant integrability, and the exact
middle-limit integral are then assembled here.
-/

namespace GppRaisedBoxMiddleDCT

open MeasureTheory Filter Real
open scoped Interval Topology
open GppRaisedBoxConcreteMoment
open GppRaisedBoxMiddleDCTPrep
open GppRaisedBoxMiddleMeasurability

/-- On the physical middle interval, the already-integrated inner slice is
eventually dominated by the `x2`-constant middle majorant. -/
theorem eventually_middle_inner_norm_le_majorant
    {δ S T x1 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hS : 0 < S) (hT : 0 < T)
    (hx10 : 0 < x1) (hx11 : x1 < 1) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∀ᵐ x2 : ℝ ∂volume, x2 ∈ Ι (0 : ℝ) (1 - x1) →
        ‖∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
            integrand ε S T x1 x2 x3‖ ≤
          middleMajorant δ S x1 := by
  have hε : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < δ :=
    (nhdsGT_basis 0).mem_of_mem hδ0
  filter_upwards [hε] with ε hε
  filter_upwards with x2
  intro hx2mem
  have hB : 0 ≤ 1 - x1 := by linarith
  rw [Set.uIoc_of_le hB] at hx2mem
  have hx2 : 0 ≤ x2 := hx2mem.1.le
  have hL0 : 0 ≤ 1 - x1 - x2 := by linarith [hx2mem.2]
  have hL1 : 1 - x1 - x2 ≤ 1 := by linarith
  exact inner_integral_norm_le_middleMajorant
    hδ0 hδ1 hS hT hx10 hx2 rfl hL0 hL1 hε.1.le hε.2.le

/-- Almost-everywhere pointwise convergence of the `x2` integrand after the
inner `x3` DCT. -/
theorem ae_middle_inner_tendsto_affine_length
    {δ S T x1 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hS : 0 < S) (hT : 0 < T)
    (hx10 : 0 < x1) (hx11 : x1 < 1) :
    ∀ᵐ x2 : ℝ ∂volume, x2 ∈ Ι (0 : ℝ) (1 - x1) →
      Tendsto
        (fun ε : ℝ =>
          ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
            integrand ε S T x1 x2 x3)
        (𝓝[>] 0) (𝓝 (1 - x1 - x2)) := by
  filter_upwards with x2
  intro hx2mem
  have hB : 0 ≤ 1 - x1 := by linarith
  rw [Set.uIoc_of_le hB] at hx2mem
  exact inner_slice_tendsto_affine_length
    hδ0 hδ1 hS hT hx10 hx2mem.1.le (by linarith [hx2mem.2])

/-- The variable-endpoint inner integral is AE strongly measurable on the
physical middle interval. -/
theorem middle_inner_aestronglyMeasurable
    (ε S T x1 : ℝ) (hx11 : x1 < 1) :
    AEStronglyMeasurable
      (fun x2 : ℝ =>
        ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
          integrand ε S T x1 x2 x3)
      (volume.restrict (Ι (0 : ℝ) (1 - x1))) := by
  let g : ℝ → ℝ := fun x2 =>
    ∫ x3 : ℝ,
      (innerRegion x1).indicator
        (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2) (x2, x3)
  have hg : AEStronglyMeasurable g
      (volume.restrict (Ι (0 : ℝ) (1 - x1))) :=
    (wholeLine_inner_integral_stronglyMeasurable ε S T x1).aestronglyMeasurable.restrict
  apply hg.congr
  change ∀ᵐ x2 : ℝ ∂volume.restrict (Ι (0 : ℝ) (1 - x1)),
    g x2 =
      ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
        integrand ε S T x1 x2 x3
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards with x2 hx2mem
  have hB : 0 ≤ 1 - x1 := by linarith
  rw [Set.uIoc_of_le hB] at hx2mem
  exact wholeLine_inner_integral_eq_intervalIntegral (by linarith [hx2mem.2])

/-- The middle DCT itself with only the concrete physical hypotheses: the
`x2`-integrated inner slice converges to the area of the affine triangle,
`(1-x1)^2/2`. -/
theorem middle_integral_tendsto
    {δ S T x1 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hS : 0 < S) (hT : 0 < T)
    (hx10 : 0 < x1) (hx11 : x1 < 1) :
    Tendsto
      (fun ε : ℝ =>
        ∫ x2 : ℝ in (0 : ℝ)..(1 - x1),
          ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
            integrand ε S T x1 x2 x3)
      (𝓝[>] 0) (𝓝 ((1 - x1) ^ 2 / 2)) := by
  have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable
        (fun x2 : ℝ =>
          ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
            integrand ε S T x1 x2 x3)
        (volume.restrict (Ι (0 : ℝ) (1 - x1))) :=
    Filter.Eventually.of_forall fun ε =>
      middle_inner_aestronglyMeasurable ε S T x1 hx11
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _x2 : ℝ => middleMajorant δ S x1)
    hmeas
    (eventually_middle_inner_norm_le_majorant
      hδ0 hδ1 hS hT hx10 hx11)
    (middleMajorant_intervalIntegrable δ S x1 0 (1 - x1))
    (ae_middle_inner_tendsto_affine_length
      hδ0 hδ1 hS hT hx10 hx11)
  simpa [affine_middle_limit_integral] using h

end GppRaisedBoxMiddleDCT

#print axioms GppRaisedBoxMiddleDCT.eventually_middle_inner_norm_le_majorant
#print axioms GppRaisedBoxMiddleDCT.ae_middle_inner_tendsto_affine_length
#print axioms GppRaisedBoxMiddleDCT.middle_inner_aestronglyMeasurable
#print axioms GppRaisedBoxMiddleDCT.middle_integral_tendsto
