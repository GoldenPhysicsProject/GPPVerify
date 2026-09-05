import Mathlib.Tactic
import GppVerify.CelestialHolography.IncidenceKernelGoogly

/-!
# Tagged ambitwistor parity without a pointwise V-star/V identification

Flat projective ambitwistor space is the incidence quadric of a projective twistor and a
projective dual twistor,

  (Z,W) in PT x PT*,   Z.W = 0.

The two factors are different representation types.  Even though the coordinate model
uses the same four real coordinates for each, this file keeps the chirality tags distinct
so that factor exchange cannot be mistaken for a canonical identification `V ≅ V*`.

The parity-like operation is therefore a map from an oriented/tagged ambitwistor pair to
an oppositely tagged pair with the two projections exchanged.  Applying the reverse
exchange returns the original pair exactly.

This is a finite-dimensional incidence statement.  It does not assert that this tagged
exchange is already the physical curved-space orientation reversal or CPT operation.
-/

namespace GppTaggedAmbitwistorParity

open GppTwistorAnnihilatorIncidence
open GppIncidenceKernelGoogly

/-- Ordinary-twistor coordinate module, tagged separately from its dual. -/
structure Twistor where
  val : V4
  deriving DecidableEq

/-- Dual-twistor coordinate module. -/
structure DualTwistor where
  val : V4
  deriving DecidableEq

/-- Canonical pairing uses only the evaluation/incidence pairing between the two tags. -/
def pairing (z : Twistor) (w : DualTwistor) : ℝ := pair4 z.val w.val

/-- One orientation/tagging of projective ambitwistor incidence before projectivization. -/
structure Ambitwistor where
  z : Twistor
  w : DualTwistor
  incident : pairing z w = 0

/-- Opposite tagging: the dual projection is written first.  No coercion identifies the
underlying representation types. -/
structure OppositeAmbitwistor where
  w : DualTwistor
  z : Twistor
  incident : pairing z w = 0

/-- Exchange the two chiral projections while retaining their types. -/
def exchange (a : Ambitwistor) : OppositeAmbitwistor :=
  ⟨a.w, a.z, a.incident⟩

/-- Reverse the tagged exchange. -/
def exchangeBack (a : OppositeAmbitwistor) : Ambitwistor :=
  ⟨a.z, a.w, a.incident⟩

/-- Tagged chirality exchange is exactly involutive. -/
theorem exchangeBack_exchange (a : Ambitwistor) :
    exchangeBack (exchange a) = a := by
  cases a
  rfl

/-- And likewise starting from the opposite tagging. -/
theorem exchange_exchangeBack (a : OppositeAmbitwistor) :
    exchange (exchangeBack a) = a := by
  cases a
  rfl

/-- A graph-line twistor representative with its annihilator dual-line representative
canonically defines an ambitwistor incidence pair. -/
def fromGraphAnnihilator
    (a b c d r s t u : ℝ) : Ambitwistor :=
  { z := ⟨lineVector a b c d r s⟩
    w := ⟨dualLineVector a b c d t u⟩
    incident := by
      exact line_dualLine_pair_zero a b c d r s t u }

/-- The factor exchange of the canonical graph/annihilator pair simply reverses which
chiral projection is listed first; it does not alter either representative. -/
theorem exchange_fromGraphAnnihilator_components
    (a b c d r s t u : ℝ) :
    (exchange (fromGraphAnnihilator a b c d r s t u)).w.val =
        dualLineVector a b c d t u ∧
    (exchange (fromGraphAnnihilator a b c d r s t u)).z.val =
        lineVector a b c d r s := by
  exact ⟨rfl,rfl⟩

/-- The underlying two projections survive a parity exchange separately.  In particular,
exchange is not a construction of one projection from the other. -/
theorem projections_preserved_under_round_trip (a : Ambitwistor) :
    (exchangeBack (exchange a)).z = a.z ∧
    (exchangeBack (exchange a)).w = a.w := by
  rw [exchangeBack_exchange]
  exact ⟨rfl,rfl⟩

end GppTaggedAmbitwistorParity
