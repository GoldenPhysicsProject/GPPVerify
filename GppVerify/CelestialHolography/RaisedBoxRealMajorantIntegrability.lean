import GppVerify.CelestialHolography.RaisedBoxConcreteMoment
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Tactic

/-!
# Raised-box real majorant: endpoint integrability

The regulator DCT for the concrete raised scalar box requires the singular
one-channel majorant

  1 + (S x1 x3)^(-delta),

with `0 < delta < 1`.  The only genuine endpoint singularities are the real
powers `x1^(-delta)` and `x3^(-delta)`.  This file records the exact one-variable
Lebesgue certificate used by the subsequent nested-simplex Tonelli/DCT layer.
-/

namespace GppRaisedBoxRealMajorantIntegrability

open MeasureTheory Real
open scoped Interval

/-- For `delta < 1`, the endpoint singularity `x^(-delta)` is Lebesgue
interval-integrable.  In particular this covers the physical DCT range
`0 < delta < 1`. -/
theorem neg_rpow_intervalIntegrable {δ a b : ℝ} (hδ : δ < 1) :
    IntervalIntegrable (fun x : ℝ => x ^ (-δ : ℝ)) volume a b := by
  exact intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -δ)

/-- Unit-interval specialization used for each singular Feynman parameter. -/
theorem neg_rpow_unit_intervalIntegrable {δ : ℝ} (hδ : δ < 1) :
    IntervalIntegrable (fun x : ℝ => x ^ (-δ : ℝ)) volume 0 1 :=
  neg_rpow_intervalIntegrable hδ

/-- The same endpoint certificate holds on every nonnegative affine simplex
slice `[0,L]`; no lower bound on `L` is required by the interval formulation. -/
theorem neg_rpow_affine_slice_intervalIntegrable
    {δ L : ℝ} (hδ : δ < 1) :
    IntervalIntegrable (fun x : ℝ => x ^ (-δ : ℝ)) volume 0 L :=
  neg_rpow_intervalIntegrable hδ

end GppRaisedBoxRealMajorantIntegrability

#print axioms GppRaisedBoxRealMajorantIntegrability.neg_rpow_intervalIntegrable
#print axioms GppRaisedBoxRealMajorantIntegrability.neg_rpow_unit_intervalIntegrable
#print axioms GppRaisedBoxRealMajorantIntegrability.neg_rpow_affine_slice_intervalIntegrable
