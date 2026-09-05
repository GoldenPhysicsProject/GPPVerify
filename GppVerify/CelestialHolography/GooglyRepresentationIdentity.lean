import Mathlib.Tactic
import GppVerify.CelestialHolography.TwistorWeightDuality
import GppVerify.CelestialHolography.TwistorRepresentationConvention
import GppVerify.CelestialHolography.SplitSignaturePenroseFourierSquare

/-!
# Same-state representation identity behind the split linear googly

In split signature a single momentum-space massless state can be represented either on
twistor space or on dual twistor space by choosing which spinor is half-Fourier transformed.
The two representations are related by the full four-dimensional Fourier transform.

There are two facts which must not be conflated:

* physically, the two transforms start from the same momentum state and reconstruct the
  same bulk solution;
* numerically, the ordinary- and dual-twistor homogeneities can look like opposite-helicity
  weights if one forgets which twistor chirality carries the degree.

The side-aware convention is formalized in `TwistorRepresentationConvention`: degree
`2h-2` on dual twistor space and degree `-2h-2` on ordinary twistor space describe the
same physical helicity `h`.  Thus a physical helicity flip does not follow from the bare
integer reflection `k ↦ -k-4`.  Orientation reversal, if used, is an additional geometric
operation.

This file formalizes those exact algebraic/categorical statements, not the analytic
Fourier integral or an orientation-reversal theorem.
-/

namespace GppGooglyRepresentationIdentity

open GppTwistorWeightDuality
open GppTwistorRepresentationConvention
open GppSplitPenroseFourierSquare

/-- Legacy pair of homogeneous degrees.  Interpreted side-aware, the first component is
the dual-twistor weight and the second the ordinary-twistor weight of the same state. -/
def sameStateWeights (n : ℤ) : ℤ × ℤ :=
  (twistorWeight n, dualTwistorWeight n)

/-- Numerical convention identity only: the ordinary-twistor degree of physical helicity
`n/2` equals the dual-twistor degree assigned to `-n/2`.  This is not a physical
helicity-flip theorem because the twistor side differs. -/
theorem same_state_dual_weight_looks_opposite (n : ℤ) :
    (sameStateWeights n).2 = twistorWeight (-n) := by
  exact dualWeight_eq_oppositeHelicityWeight n

/-- The rank-four Fourier reflection carries the dual-twistor homogeneous degree of the
state to its ordinary-twistor homogeneous degree. -/
theorem same_state_fourier_weight (n : ℤ) :
    fourierWeight (sameStateWeights n).1 = (sameStateWeights n).2 := by
  exact fourierWeight_twistor_eq_dual n

/-- Side-aware restatement: Fourier changes twistor representation while retaining the
same physical doubled-helicity label `n`. -/
theorem same_state_fourier_weight_side_aware (n : ℤ) :
    fourierWeight (dualTwistorPhysicalWeight n) = ordinaryTwistorPhysicalWeight n := by
  exact fourier_dual_to_ordinary_same_helicity n

/-- Applying the representation change twice restores the original homogeneous degree. -/
theorem same_state_weight_round_trip (n : ℤ) :
    fourierWeight (fourierWeight (sameStateWeights n).1) = (sameStateWeights n).1 := by
  exact fourierWeight_involutive (twistorWeight n)

/-- For a common momentum bridge, the ordinary and dual twistor representatives of one
momentum state reconstruct exactly the same bulk solution. -/
theorem same_momentum_state_same_bulk
    {Mom Tw TwDual Bulk : Type*}
    (B : CommonMomentumBridge Mom Tw TwDual Bulk)
    (hinv : ∀ m, B.fromTw (B.toTw m) = m)
    (m : Mom) :
    B.dualPenrose (B.fullFourier (B.toTw m)) = B.penrose (B.toTw m) := by
  exact two_penrose_representations_same_bulk B hinv m

/-- Linear split-signature resolution pattern: one state, two Fourier-related twistor
representations, same bulk tensor.  The final equality is explicitly a numerical
cross-convention identity, not a physical helicity-flip assertion. -/
theorem one_state_two_representations
    {Mom Tw TwDual Bulk : Type*}
    (B : CommonMomentumBridge Mom Tw TwDual Bulk)
    (hinv : ∀ m, B.fromTw (B.toTw m) = m)
    (m : Mom) (n : ℤ) :
    B.dualPenrose (B.fullFourier (B.toTw m)) = B.penrose (B.toTw m) ∧
    dualTwistorWeight n = twistorWeight (-n) := by
  exact ⟨same_momentum_state_same_bulk B hinv m,
    dualWeight_eq_oppositeHelicityWeight n⟩

end GppGooglyRepresentationIdentity
