import GppVerify.CelestialHolography.RaisedBoxRealOuterDomination
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Raised-box real majorant: outer-kernel integrability

The endpoint certificate `x ^ (-δ)` is interval-integrable for `δ < 1`, and
`RaisedBoxRealOuterDomination` proves that the post-middle outer kernel

  x ^ (-δ) * (1 - x) ^ (2 - δ)

has norm bounded by that endpoint singularity on `[0,1]`.  This file packages
those two facts into the interval-integrability statement needed by the final
nested Fubini/Tonelli and dominated-convergence layer on the pinned Mathlib API.
-/

namespace GppRaisedBoxRealOuterIntegrability

open MeasureTheory Real
open scoped Interval
open GppRaisedBoxRealMajorantIntegrability
open GppRaisedBoxRealOuterDomination

/-- The real outer Beta kernel left after the exact `x3` and `x2` integrations
is Lebesgue interval-integrable throughout the range `δ < 1`. -/
theorem outer_kernel_intervalIntegrable {δ : ℝ} (hδ : δ < 1) :
    IntervalIntegrable
      (fun x : ℝ => x ^ (-δ : ℝ) * (1 - x) ^ (2 - δ : ℝ))
      volume 0 1 := by
  apply (neg_rpow_unit_intervalIntegrable hδ).mono_fun'
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
    exact norm_outer_kernel_le_endpoint hδ hx'.1.le hx'.2

/-- Physical raised-box specialization.  The strict lower bound is part of the
regulator-majorant hypotheses even though outer integrability itself only uses
`δ < 1`. -/
theorem outer_kernel_intervalIntegrable_physical
    {δ : ℝ} (_hδ0 : 0 < δ) (hδ1 : δ < 1) :
    IntervalIntegrable
      (fun x : ℝ => x ^ (-δ : ℝ) * (1 - x) ^ (2 - δ : ℝ))
      volume 0 1 :=
  outer_kernel_intervalIntegrable hδ1

end GppRaisedBoxRealOuterIntegrability

#print axioms GppRaisedBoxRealOuterIntegrability.outer_kernel_intervalIntegrable
#print axioms GppRaisedBoxRealOuterIntegrability.outer_kernel_intervalIntegrable_physical
