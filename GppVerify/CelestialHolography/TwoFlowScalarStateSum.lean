import GppVerify.CelestialHolography.FourPointMHVBubbleSubtractionAlgebra
import Mathlib.Tactic

/-!
# Two-orientation scalar-flow state sum

The adjacent-MHV bubble subtraction audit leaves one specific physics convention
outside the proved rational algebra: a complex scalar contribution is assembled from
two oriented scalar flows.  This file does not assume that physical identification.
Instead it makes the finite state-space bookkeeping explicit.

For a two-element orientation space, if both orientations contribute the same scalar
coefficient `C`, their state sum is exactly `2*C`.  Composing this finite theorem with
the already-proved one-flow bubble coefficient yields the frame target.  Thus the
remaining amplitude-specific input is reduced to the equality of the two oriented
flow contributions with the one-flow coefficient, not an unexplained multiplicity
factor.
-/

namespace GppTwoFlowScalarStateSum

open GppFourPointMHVBubbleSubtractionAlgebra

/-- The two oriented flow labels. -/
inductive FlowOrientation
  | forward
  | backward
  deriving DecidableEq, Fintype

/-- Constant contribution attached to each of the two flow orientations. -/
def equalFlowContribution (C : ℝ) : FlowOrientation → ℝ := fun _ => C

/-- Exact finite-state count: two equal oriented flows contribute twice one flow. -/
theorem sum_equal_flows (C : ℝ) :
    ∑ o : FlowOrientation, equalFlowContribution C o = 2 * C := by
  simp [equalFlowContribution, FlowOrientation]

/-- If both physical orientations agree with the one-flow bubble coefficient, their
explicit finite state sum is the phase-normal frame target. -/
theorem oriented_bubble_sum_eq_frame_target (u : ℝ) :
    ∑ o : FlowOrientation, equalFlowContribution (oneFlowBubbleReal u) o =
      (2 / 3 : ℝ) * (2 * frameS12 u - 3) := by
  rw [sum_equal_flows]
  exact two_mul_oneFlow_eq_frame_target u

/-- More general interface: any orientation-dependent contribution known to equal the
one-flow result for both labels has the same total.  This states the remaining physics
input directly at the state-space level. -/
theorem oriented_bubble_sum_eq_frame_target_of_pointwise
    (u : ℝ) (C : FlowOrientation → ℝ)
    (hC : ∀ o, C o = oneFlowBubbleReal u) :
    ∑ o : FlowOrientation, C o =
      (2 / 3 : ℝ) * (2 * frameS12 u - 3) := by
  calc
    ∑ o : FlowOrientation, C o =
        ∑ o : FlowOrientation, equalFlowContribution (oneFlowBubbleReal u) o := by
      apply Finset.sum_congr rfl
      intro o ho
      simp [equalFlowContribution, hC o]
    _ = (2 / 3 : ℝ) * (2 * frameS12 u - 3) :=
      oriented_bubble_sum_eq_frame_target u

end GppTwoFlowScalarStateSum

#print axioms GppTwoFlowScalarStateSum.sum_equal_flows
#print axioms GppTwoFlowScalarStateSum.oriented_bubble_sum_eq_frame_target
#print axioms GppTwoFlowScalarStateSum.oriented_bubble_sum_eq_frame_target_of_pointwise
