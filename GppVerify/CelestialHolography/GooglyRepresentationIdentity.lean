import Mathlib.Tactic
import GppVerify.CelestialHolography.TwistorWeightDuality
import GppVerify.CelestialHolography.TwistorRepresentationConvention
import GppVerify.CelestialHolography.SplitSignaturePenroseFourierSquare
import GppVerify.CelestialHolography.OrientationOnlyGooglyNoGo

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

The final section combines this same-state Fourier bridge with the existing orientation-only
no-go.  The result is an exact obstruction: Fourier representation change plus orientation
reversal can exchange the two pure-chiral labelings of one field, but cannot manufacture a
generic field with two independently nonzero chiral components.  Hence this linear
representation theorem is not by itself a nonlinear googly solution.

This file formalizes those exact algebraic/categorical statements, not the analytic
Fourier integral or an orientation-reversal construction on twistor cohomology.
-/

namespace GppGooglyRepresentationIdentity

open GppTwistorWeightDuality
open GppTwistorRepresentationConvention
open GppSplitPenroseFourierSquare
open GppOrientationOnlyGooglyNoGo

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

/-! ## Exact limit of same-state Fourier plus orientation reversal -/

/-- If the source Penrose field is purely plus-chiral, the Fourier-related dual-twistor
representative reconstructs that same pure field.  Reversing orientation therefore gives
the purely minus-chiral labeling and nothing more. -/
theorem fourier_then_orientation_of_pure_plus
    {Mom Tw TwDual A : Type*} [Zero A]
    (B : CommonMomentumBridge Mom Tw TwDual (ChiralPair A))
    (z : Tw) (a : A)
    (hsrc : B.penrose z = ChiralPair.mk a 0) :
    reverseOrientation (B.dualPenrose (B.fullFourier z)) = ChiralPair.mk 0 a := by
  rw [B.penrose_fullFourier_commutes z, hsrc]
  rfl

/-- Same-state Fourier representation change plus orientation reversal cannot produce a
generic non-self-dual pair `(a,b)` with both components nonzero from a pure source.
This is the precise obstruction separating the linear representation identity from the
nonlinear googly problem. -/
theorem same_state_fourier_orientation_excludes_generic
    {Mom Tw TwDual A : Type*} [Zero A]
    (B : CommonMomentumBridge Mom Tw TwDual (ChiralPair A))
    (z : Tw) (a b : A) (ha : a ≠ 0) (hb : b ≠ 0)
    (hsrc : B.penrose z = ChiralPair.mk a 0) :
    reverseOrientation (B.dualPenrose (B.fullFourier z)) ≠ ChiralPair.mk a b := by
  rw [B.penrose_fullFourier_commutes z, hsrc]
  exact generic_pair_not_from_reversing_pure_plus a b ha hb

/-- The two representatives available from a pure source through identity/Fourier and
orientation relabeling exclude every genuinely two-chiral field. -/
theorem same_state_orientation_orbit_excludes_generic
    {Mom Tw TwDual A : Type*} [Zero A]
    (B : CommonMomentumBridge Mom Tw TwDual (ChiralPair A))
    (z : Tw) (a b : A) (ha : a ≠ 0) (hb : b ≠ 0)
    (hsrc : B.penrose z = ChiralPair.mk a 0) :
    ChiralPair.mk a b ≠ B.dualPenrose (B.fullFourier z) ∧
    ChiralPair.mk a b ≠ reverseOrientation (B.dualPenrose (B.fullFourier z)) := by
  rw [B.penrose_fullFourier_commutes z, hsrc]
  exact orientation_orbit_of_pure_excludes_generic a b ha hb

end GppGooglyRepresentationIdentity
