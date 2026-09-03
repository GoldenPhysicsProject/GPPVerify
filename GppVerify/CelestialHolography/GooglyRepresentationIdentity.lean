import Mathlib.Tactic
import GppVerify.CelestialHolography.TwistorWeightDuality
import GppVerify.CelestialHolography.SplitSignaturePenroseFourierSquare

/-!
# Same-state representation identity behind the split linear googly

In split signature a single momentum-space massless state can be represented either on
twistor space or on dual twistor space by choosing which spinor is half-Fourier transformed.
The two representations are related by the full four-dimensional Fourier transform.

There are two facts which must not be conflated:

* physically, the two transforms start from the same momentum state and reconstruct the
  same bulk solution;
* homogeneously, the dual-twistor weight for helicity `h` is numerically the ordinary
  twistor weight assigned to helicity `-h`.

Thus an apparent helicity flip can arise from changing between twistor and dual-twistor
conventions without changing the underlying momentum state.  Orientation reversal can
then relabel the same real split-signature tensor from SD to ASD.  This file formalizes
those exact algebraic/categorical statements, not the analytic Fourier integral.
-/

namespace GppGooglyRepresentationIdentity

open GppTwistorWeightDuality
open GppSplitPenroseFourierSquare

/-- Ordinary twistor and dual-twistor homogeneities of the same doubled-helicity state. -/
def sameStateWeights (n : ℤ) : ℤ × ℤ :=
  (twistorWeight n, dualTwistorWeight n)

/-- The dual-twistor homogeneity of a physical helicity `n/2` state is exactly the
ordinary-twistor homogeneity associated numerically with helicity `-n/2`. -/
theorem same_state_dual_weight_looks_opposite (n : ℤ) :
    (sameStateWeights n).2 = twistorWeight (-n) := by
  exact dualWeight_eq_oppositeHelicityWeight n

/-- Equivalently the full rank-four Fourier reflection carries the ordinary twistor
weight of the state to its dual-twistor weight. -/
theorem same_state_fourier_weight (n : ℤ) :
    fourierWeight (sameStateWeights n).1 = (sameStateWeights n).2 := by
  exact fourierWeight_twistor_eq_dual n

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
representations, same bulk tensor, opposite ordinary-twistor weight label. -/
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
