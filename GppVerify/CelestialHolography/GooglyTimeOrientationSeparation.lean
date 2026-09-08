import Mathlib.Tactic
import GppVerify.CelestialHolography.SpinProductCenterTimeOrientation
import GppVerify.CelestialHolography.SpinCenterRepresentationParity

/-!
# Googly chirality exchange is distinct from time/worldline orientation reversal

The doubled spin geometry contains two different Z2 operations that should not be conflated:

1. factor exchange

     G : (L,R) -> (R,L),

   which swaps spinor bidegrees `(a,b) <-> (b,a)` and hence exchanges the two Weyl-curvature
   chiralities `(4,0) <-> (0,4)`;

2. relative-center reversal

     Trel : (sL,sR) -> (-sL,sR)

   (or equivalently the right lift modulo the diagonal center), which reverses the vector
   orientation character `t=sL*sR`.

Factor exchange preserves `t`, because multiplication is symmetric.  Relative-center
reversal changes `t` but leaves even-degree chiral curvatures center-even.  Their composition
has an order-four spin lift whose square is the diagonal center.

This gives a useful structural separation for the googly programme: googly exchange can swap
`W+` and `W-` without itself reversing worldline/time orientation, while a CPT-like operation
may additionally act on the relative center and the gauge fibre.
-/

namespace GppGooglyTimeOrientationSeparation

open GppSpinProductCenterTimeOrientation
open GppSpinCenterRepresentationParity

/-- Exchange the two center signs along with the two spin factors. -/
def exchangeCenterSigns (s : ℝ × ℝ) : ℝ × ℝ := (s.2,s.1)

/-- One representative of relative-center/worldline orientation reversal. -/
def relativeCenterFlip (s : ℝ × ℝ) : ℝ × ℝ := (-s.1,s.2)

/-- Their composition, an order-four lift on the sign pair. -/
def quarterCenterLift (s : ℝ × ℝ) : ℝ × ℝ :=
  exchangeCenterSigns (relativeCenterFlip s)

/-- Googly/factor exchange preserves the vector time-orientation character. -/
theorem factor_exchange_preserves_vector_orientation (sL sR : ℝ) :
    vectorCenterCharacter (exchangeCenterSigns (sL,sR)).1
      (exchangeCenterSigns (sL,sR)).2 = vectorCenterCharacter sL sR := by
  simp [exchangeCenterSigns, vectorCenterCharacter, mul_comm]

/-- Relative-center reversal flips that character. -/
theorem relative_center_flip_reverses_vector_orientation (sL sR : ℝ) :
    vectorCenterCharacter (relativeCenterFlip (sL,sR)).1
      (relativeCenterFlip (sL,sR)).2 = - vectorCenterCharacter sL sR := by
  simp [relativeCenterFlip, vectorCenterCharacter]

/-- The combined lift acts as `(sL,sR) -> (sR,-sL)`. -/
theorem quarterCenterLift_apply (sL sR : ℝ) :
    quarterCenterLift (sL,sR) = (sR,-sL) := by
  rfl

/-- Two combined operations give the diagonal center. -/
theorem quarterCenterLift_sq (sL sR : ℝ) :
    quarterCenterLift (quarterCenterLift (sL,sR)) = (-sL,-sR) := by
  rfl

/-- Four close exactly. -/
theorem quarterCenterLift_four (sL sR : ℝ) :
    quarterCenterLift (quarterCenterLift (quarterCenterLift (quarterCenterLift (sL,sR))))
      = (sL,sR) := by
  rfl

/-- One combined quarter-lift reverses vector orientation, while its square becomes
vector-invisible because the diagonal center has product `+1`. -/
theorem quarterLift_orientation_pattern (sL sR : ℝ) :
    vectorCenterCharacter (quarterCenterLift (sL,sR)).1
      (quarterCenterLift (sL,sR)).2 = - vectorCenterCharacter sL sR ∧
    vectorCenterCharacter (quarterCenterLift (quarterCenterLift (sL,sR))).1
      (quarterCenterLift (quarterCenterLift (sL,sR))).2 = vectorCenterCharacter sL sR := by
  simp [quarterCenterLift, exchangeCenterSigns, relativeCenterFlip, vectorCenterCharacter]

/-- Representation-theoretic googly action: factor exchange swaps the Weyl bidegrees. -/
theorem googly_swaps_weyl_bidegrees :
    ((4,0) : ℕ × ℕ) = ((0,4).2,(0,4).1) := by
  rfl

/-- Yet each chiral Weyl curvature is center-even under the relative orientation flip. -/
theorem relative_center_invisible_to_weyl_curvatures :
    centerCharacter 4 0 (-1) 1 = 1 ∧ centerCharacter 0 4 1 (-1) = 1 := by
  exact ⟨left_weyl_curvature_center_even, right_weyl_curvature_center_even⟩

end GppGooglyTimeOrientationSeparation
