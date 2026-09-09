import Mathlib.Tactic
import GppVerify.StandardModel.FourOrientationGaugeProjection

/-!
# A standard U(1) charge representation on the diagonal orientation quotient

The four-lift carrier by itself is only useful if it can reproduce the ordinary two-sector
charge representation after the diagonal identification.  This file constructs exactly
that representation.

For a nonzero complex phase/scale `z`, act on the four kinematic lifts by

    (++,+-,-+,--) -> (z, z^{-1}, z^{-1}, z).

Thus the action depends only on the relational grading `χ=q*t`; it commutes with the
diagonal reversal `D` and therefore descends to the `D`-even physical candidate subspace.
On the exact parameterization

    physicalLift(a,b) = (a,b,b,a)

it becomes

    (a,b) -> (z a, z^{-1} b),

which is precisely the standard pair of conjugate one-dimensional U(1) representations.

This gives a concrete consistency mechanism: two hidden microscopic orientation lifts per
relational sector need not add low-energy charge species if the diagonal reversal is gauge;
the quotient carries exactly the usual +/- charge representation.  The remaining physical
problem is to derive this quotient/action from the Lorentz-spin/gauge bundle rather than
postulate it.
-/

namespace GppRelationalU1GaugeRepresentation

open GppFourOrientationGaugeProjection

/-- Relational U(1)/C* action on the four kinematic orientation lifts. -/
def relationalScale (z : ℂ) (v : Orientation4) : Orientation4 :=
  (z * v.1, z⁻¹ * v.2.1, z⁻¹ * v.2.2.1, z * v.2.2.2)

/-- Identity element acts trivially. -/
theorem relationalScale_one (v : Orientation4) :
    relationalScale 1 v = v := by
  rcases v with ⟨a,b,c,d⟩
  simp [relationalScale]

/-- Multiplication of group parameters composes the actions. -/
theorem relationalScale_mul (z w : ℂ) (v : Orientation4) :
    relationalScale z (relationalScale w v) =
      relationalScale (z*w) v := by
  rcases v with ⟨a,b,c,d⟩
  simp [relationalScale, mul_assoc]
  constructor
  · ring
  · constructor
    · rw [mul_inv_rev]
      ring
    · constructor
      · rw [mul_inv_rev]
        ring
      · ring

/-- The relational gauge action commutes with simultaneous microscopic reversal. -/
theorem relationalScale_commutes_diag (z : ℂ) (v : Orientation4) :
    diagReverse (relationalScale z v) =
      relationalScale z (diagReverse v) := by
  rcases v with ⟨a,b,c,d⟩
  rfl

/-- Therefore the diagonal-even candidate physical subspace is preserved. -/
theorem relationalScale_preserves_even (z : ℂ) (v : Orientation4)
    (h : diagReverse v = v) :
    diagReverse (relationalScale z v) = relationalScale z v := by
  rw [relationalScale_commutes_diag, h]

/-- Exact descended action: the two physical amplitudes carry conjugate weights. -/
theorem relationalScale_on_physicalLift (z a b : ℂ) :
    relationalScale z (physicalLift a b) =
      physicalLift (z*a) (z⁻¹*b) := by
  rfl

/-- Matter basis carries weight `z`. -/
theorem matterLift_charge_weight (z : ℂ) :
    relationalScale z matterLift =
      physicalLift z 0 := by
  simp [matterLift, relationalScale, physicalLift]

/-- Antimatter basis carries the conjugate/inverse weight `z^{-1}`. -/
theorem antimatterLift_charge_weight (z : ℂ) :
    relationalScale z antimatterLift =
      physicalLift 0 z⁻¹ := by
  simp [antimatterLift, relationalScale, physicalLift]

/-- The diagonal reversal is in the kernel of the observable relational sign: it leaves
both physical charge sectors fixed pointwise, whereas either half flip exchanges them. -/
theorem diagonal_kernel_half_flip_exchange_package :
    diagReverse matterLift = matterLift ∧
    diagReverse antimatterLift = antimatterLift ∧
    chargeFlip matterLift = antimatterLift ∧
    temporalFlip matterLift = antimatterLift := by
  exact ⟨rfl,rfl,rfl,rfl⟩

end GppRelationalU1GaugeRepresentation
