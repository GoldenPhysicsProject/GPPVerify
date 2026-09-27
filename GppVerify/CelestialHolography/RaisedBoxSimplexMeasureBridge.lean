import GppVerify.CelestialHolography.RaisedBoxSimplexBetaLayer
import Mathlib.Tactic

/-!
# Raised-box simplex measure bridge

The exact inner affine slice and the outer unit Beta kernel are already
formalized separately.  This file packages the integrability statement needed
by the Fubini/Tonelli layer after the inner slice has been reduced to its
constant `B(1-delta,2)` factor.
-/

namespace GppRaisedBoxSimplexMeasureBridge

open Complex
open scoped Interval
open GppRaisedBoxSimplexBetaLayer

/-- The reduced outer integrand remains interval-integrable after multiplying
by the constant inner Beta factor. -/
theorem outer_reduced_beta_convergent {δ : ℝ} (hδ : δ < 1) :
    IntervalIntegrable
      (fun x : ℝ =>
        ((x : ℂ) ^ ((((1 - δ : ℝ) : ℂ) - 1)) *
          (1 - (x : ℂ)) ^ ((((3 - δ : ℝ) : ℂ) - 1))) *
          betaIntegral (((1 - δ : ℝ) : ℂ)) 2)
      MeasureTheory.volume 0 1 := by
  exact (outer_beta_convergent hδ).mul_const
    (betaIntegral (((1 - δ : ℝ) : ℂ)) 2)

/-- Every nondegenerate inner affine simplex slice is interval-integrable.  This
re-exports the scaled-Beta certificate at the exact interface used by Tonelli. -/
theorem inner_slice_convergent {δ x : ℝ} (hδ : δ < 1) (hx : x < 1) :
    IntervalIntegrable
      (fun y : ℝ =>
        (y : ℂ) ^ ((((1 - δ : ℝ) : ℂ) - 1)) *
          (((1 - x : ℝ) : ℂ) - y) ^ (((2 : ℂ) - 1)))
      MeasureTheory.volume 0 (1 - x) :=
  inner_simplex_slice_convergent hδ hx

end GppRaisedBoxSimplexMeasureBridge

#print axioms GppRaisedBoxSimplexMeasureBridge.outer_reduced_beta_convergent
#print axioms GppRaisedBoxSimplexMeasureBridge.inner_slice_convergent
