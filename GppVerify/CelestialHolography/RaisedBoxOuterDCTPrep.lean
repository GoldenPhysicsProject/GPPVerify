import GppVerify.CelestialHolography.RaisedBoxMiddleDCT
import GppVerify.CelestialHolography.RaisedBoxRealMajorantIntegrability
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Raised-box outer DCT preparation

After the completed `x2` dominated-convergence layer, the final variable is
`x1`.  A sharper Beta-shaped majorant is available elsewhere, but the outer DCT
needs only a simple integrable envelope.  On `0 < x1 < 1`,

  middleMajorant δ S x1
    = 1 + S^(-δ) x1^(-δ) / (1-δ),

and the `x2` interval has length at most one. Thus the whole double-inner slice
is dominated by a constant plus the single endpoint singularity `x1^(-δ)`,
which is interval-integrable for `δ < 1`.
-/

namespace GppRaisedBoxOuterDCTPrep

open MeasureTheory Real
open scoped Interval Topology
open GppRaisedBoxConcreteMoment
open GppRaisedBoxMiddleDCTPrep
open GppRaisedBoxRealMajorantIntegrability

/-- Simple endpoint-integrable majorant for the final `x1` DCT. -/
noncomputable def outerMajorant (δ S x1 : ℝ) : ℝ :=
  1 + (S ^ (-δ : ℝ) / (1 - δ)) * x1 ^ (-δ : ℝ)

/-- On positive physical data, the middle majorant factors into the simple
outer endpoint majorant. -/
theorem middleMajorant_eq_outerMajorant
    {δ S x1 : ℝ} (hS : 0 ≤ S) (hx1 : 0 ≤ x1) :
    middleMajorant δ S x1 = outerMajorant δ S x1 := by
  unfold middleMajorant outerMajorant
  rw [Real.mul_rpow hS hx1]
  ring

/-- The simple outer majorant is interval-integrable on `[0,1]` whenever
`δ < 1`. -/
theorem outerMajorant_intervalIntegrable
    {δ S : ℝ} (hδ : δ < 1) :
    IntervalIntegrable (fun x1 : ℝ => outerMajorant δ S x1) volume 0 1 := by
  have hconst : IntervalIntegrable (fun _x1 : ℝ => (1 : ℝ)) volume 0 1 :=
    intervalIntegrable_const
  have hpow : IntervalIntegrable (fun x1 : ℝ => x1 ^ (-δ : ℝ)) volume 0 1 :=
    neg_rpow_unit_intervalIntegrable hδ
  have hscaled : IntervalIntegrable
      (fun x1 : ℝ => (S ^ (-δ : ℝ) / (1 - δ)) * x1 ^ (-δ : ℝ))
      volume 0 1 :=
    hpow.const_mul (S ^ (-δ : ℝ) / (1 - δ))
  exact hconst.add hscaled

/-- The simple outer majorant is nonnegative on the physical range. -/
theorem outerMajorant_nonneg
    {δ S x1 : ℝ} (hδ : δ < 1) (hS : 0 ≤ S) (hx1 : 0 ≤ x1) :
    0 ≤ outerMajorant δ S x1 := by
  rw [← middleMajorant_eq_outerMajorant hS hx1]
  exact middleMajorant_nonneg hδ hS hx1

/-- At fixed `0 ≤ ε ≤ δ`, the already-integrated `(x2,x3)` slice is bounded
in norm by the simple outer majorant. -/
theorem middle_integral_norm_le_outerMajorant
    {ε δ S T x1 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hS : 0 < S) (hT : 0 < T)
    (hx10 : 0 < x1) (hx11 : x1 < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ) :
    ‖∫ x2 : ℝ in (0 : ℝ)..(1 - x1),
        ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
          integrand ε S T x1 x2 x3‖ ≤
      outerMajorant δ S x1 := by
  have hB0 : 0 ≤ 1 - x1 := by linarith
  have hbound : IntervalIntegrable
      (fun _x2 : ℝ => middleMajorant δ S x1) volume 0 (1 - x1) :=
    middleMajorant_intervalIntegrable δ S x1 0 (1 - x1)
  have hdom :
      ∀ᵐ x2 : ℝ ∂volume.restrict (Ι (0 : ℝ) (1 - x1)),
        ‖∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
            integrand ε S T x1 x2 x3‖ ≤ middleMajorant δ S x1 := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with x2 hx2mem
    rw [Set.uIoc_of_le hB0] at hx2mem
    have hx2 : 0 ≤ x2 := hx2mem.1.le
    have hL0 : 0 ≤ 1 - x1 - x2 := by linarith [hx2mem.2]
    have hL1 : 1 - x1 - x2 ≤ 1 := by linarith
    exact inner_integral_norm_le_middleMajorant
      hδ0 hδ1 hS hT hx10 hx2 rfl hL0 hL1 hε0 hεδ
  have hnorm := intervalIntegral.norm_integral_le_abs_of_norm_le hdom hbound
  rw [intervalIntegral.integral_const] at hnorm
  have hmaj : 0 ≤ middleMajorant δ S x1 :=
    middleMajorant_nonneg hδ1 hS.le hx10.le
  have hprod : 0 ≤ (1 - x1) * middleMajorant δ S x1 :=
    mul_nonneg hB0 hmaj
  rw [abs_of_nonneg hprod] at hnorm
  have hlen : 1 - x1 ≤ 1 := by linarith
  have hslice : (1 - x1) * middleMajorant δ S x1 ≤ middleMajorant δ S x1 := by
    nlinarith
  rw [middleMajorant_eq_outerMajorant hS.le hx10.le] at hslice
  exact hnorm.trans hslice

end GppRaisedBoxOuterDCTPrep

#print axioms GppRaisedBoxOuterDCTPrep.middleMajorant_eq_outerMajorant
#print axioms GppRaisedBoxOuterDCTPrep.outerMajorant_intervalIntegrable
#print axioms GppRaisedBoxOuterDCTPrep.outerMajorant_nonneg
#print axioms GppRaisedBoxOuterDCTPrep.middle_integral_norm_le_outerMajorant
