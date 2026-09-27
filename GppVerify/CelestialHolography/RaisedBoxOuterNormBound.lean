import GppVerify.CelestialHolography.RaisedBoxMiddleMeasurability
import GppVerify.CelestialHolography.RaisedBoxOuterDCTMajorant
import Mathlib.Tactic

/-!
# Raised-box outer norm bound

This file packages the exact domination needed by the final outer-coordinate
DCT.  After the certified middle DCT, the nested two-inner-coordinate integral
has norm bounded by the same explicit `x1` majorant that is already known to be
interval-integrable on `[0,1]`.
-/

namespace GppRaisedBoxOuterNormBound

open Filter Set MeasureTheory
open scoped Interval Topology
open GppRaisedBoxConcreteMoment
open GppRaisedBoxMiddleMeasurability

/-- The complete two-inner-coordinate nested raised-box integral is bounded by
`1 + (S*x1)^(-δ)/(1-δ)` throughout the strict physical outer interval. -/
theorem nestedInnerIntegral_norm_le_outerMajorant
    {δ ε S T x1 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx1lt : x1 < 1) :
    ‖∫ x2 in (0 : ℝ)..(1 - x1),
        ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
          integrand ε S T x1 x2 x3‖ ≤
      1 + (S * x1) ^ (-δ : ℝ) / (1 - δ) := by
  have hL : 0 < 1 - x1 := by linarith
  let C : ℝ := 1 + (S * x1) ^ (-δ : ℝ) / (1 - δ)
  have hAE : ∀ᵐ x2 : ℝ ∂volume.restrict (Set.uIoc (0 : ℝ) (1 - x1)),
      ‖∫ x3 in (0 : ℝ)..(1 - x1 - x2),
          integrand ε S T x1 x2 x3‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with x2 hx2mem
    rw [Set.uIoc_of_le hL.le] at hx2mem
    have hx12 : x1 + x2 ≤ 1 := by linarith [hx2mem.2]
    exact intervalInnerIntegral_norm_le_middleConstant
      hδ0 hδ1 hε0 hεδ hS hT hx1 hx2mem.1.le hx12
  have hCint : IntervalIntegrable (fun _x2 : ℝ => C) volume 0 (1 - x1) :=
    intervalIntegrable_const
  have hAbs := intervalIntegral.norm_integral_le_of_norm_le hAE hCint
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    have hden : 0 < 1 - δ := by linarith
    positivity
  have hLen : 0 ≤ 1 - x1 := hL.le
  have hLenLe : 1 - x1 ≤ 1 := by linarith
  have hEval :
      ∫ _x2 in (0 : ℝ)..(1 - x1), C = (1 - x1) * C := by
    simp
  rw [hEval] at hAbs
  rw [abs_of_nonneg (mul_nonneg hLen hCnonneg)] at hAbs
  calc
    ‖∫ x2 in (0 : ℝ)..(1 - x1),
        ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
          integrand ε S T x1 x2 x3‖ ≤ (1 - x1) * C := hAbs
    _ ≤ 1 * C := by gcongr
    _ = 1 + (S * x1) ^ (-δ : ℝ) / (1 - δ) := by simp [C]

end GppRaisedBoxOuterNormBound

#print axioms GppRaisedBoxOuterNormBound.nestedInnerIntegral_norm_le_outerMajorant
