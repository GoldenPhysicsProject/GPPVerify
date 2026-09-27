import GppVerify.CelestialHolography.RaisedBoxConcreteMoment
import Mathlib.Tactic

/-!
# Raised-box strip integral bridge

The jointly measurable two-dimensional strip representation is useful for
product-measure/Fubini arguments, while the original raised-box moment is
written with the affine variable endpoint `0 ≤ x3 ≤ 1 - x1 - x2`.

This file lifts the certified pointwise section identity to equality of the
corresponding whole-line indicator integrals.  It is the direct bridge needed
before converting the product-integral measurability theorem into the middle
DCT formulation used by the nested simplex moment.
-/

namespace GppRaisedBoxStripIntegralBridge

open GppRaisedBoxConcreteMoment

/-- Integrating a fixed `x2` section of the measurable two-dimensional simplex
strip is exactly the same as integrating the corresponding closed-interval
indicator of the original affine innermost coordinate. -/
theorem stripInnerIntegral_eq_IccIndicatorIntegral
    (ε S T x1 x2 : ℝ) :
    (∫ x3 : ℝ,
      ((innerSimplexStrip x1).indicator
        (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2)) (x2, x3)) =
    ∫ x3 : ℝ,
      (Set.Icc (0 : ℝ) (1 - x1 - x2)).indicator
        (fun y : ℝ => integrand ε S T x1 x2 y) x3 := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x3
  exact stripIntegrand_section_eq_Icc_indicator ε S T x1 x2 x3

/-- On the middle simplex range, the measurable closed-interval indicator
integral is exactly the oriented interval integral used in the original nested
raised-box moment.  The only endpoint difference is the null singleton at
`x3 = 0`, discharged by Mathlib's `integral_Icc_eq_integral_Ioc`. -/
theorem IccIndicatorIntegral_eq_intervalIntegral
    (ε S T x1 x2 : ℝ)
    (hx2 : x2 ∈ Set.Icc (0 : ℝ) (1 - x1)) :
    (∫ x3 : ℝ,
      (Set.Icc (0 : ℝ) (1 - x1 - x2)).indicator
        (fun y : ℝ => integrand ε S T x1 x2 y) x3) =
    ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2), integrand ε S T x1 x2 x3 := by
  have hle : (0 : ℝ) ≤ 1 - x1 - x2 := by
    rcases hx2 with ⟨_, hx2hi⟩
    linarith
  rw [MeasureTheory.integral_indicator measurableSet_Icc]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hle]

/-- Combining the measurable strip representation with the endpoint-null
conversion gives the exact variable-endpoint inner integral used by the middle
DCT. -/
theorem stripInnerIntegral_eq_intervalIntegral
    (ε S T x1 x2 : ℝ)
    (hx2 : x2 ∈ Set.Icc (0 : ℝ) (1 - x1)) :
    (∫ x3 : ℝ,
      ((innerSimplexStrip x1).indicator
        (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2)) (x2, x3)) =
    ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2), integrand ε S T x1 x2 x3 := by
  rw [stripInnerIntegral_eq_IccIndicatorIntegral]
  exact IccIndicatorIntegral_eq_intervalIntegral ε S T x1 x2 hx2

end GppRaisedBoxStripIntegralBridge

#print axioms GppRaisedBoxStripIntegralBridge.stripInnerIntegral_eq_IccIndicatorIntegral
#print axioms GppRaisedBoxStripIntegralBridge.IccIndicatorIntegral_eq_intervalIntegral
#print axioms GppRaisedBoxStripIntegralBridge.stripInnerIntegral_eq_intervalIntegral
