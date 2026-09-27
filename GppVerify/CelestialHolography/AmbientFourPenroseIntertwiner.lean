import Mathlib.Tactic
import GppVerify.CelestialHolography.AmbientFourDualitySpine

/-!
# Ambient-four Penrose intertwiner

This file isolates the exact logical shape needed for the GPP googly proposal.
It does not assert the analytic Penrose transform theorem.  Instead it records the
consequence once one proves that the field-level duality induced from the ambient
four-dimensional orientation is carried by the two Penrose representations to
orientation reversal of the same bulk field.

The point is to separate three levels cleanly:

* an involution `dual` on lifted/twistor data;
* two chiral projections `plus` and `minus`;
* an orientation reversal `reverse` on bulk data.

If `minus (dual x) = reverse (plus x)`, then the opposite chirality is not added by
hand: it is the other projection of the same lifted datum after the diagonal duality.
If observables are also invariant under `dual`, the two lifts represent one
operational class.
-/

namespace GppAmbientFourPenroseIntertwiner

/-- Abstract data for the proposed one-geometry/two-oriented-lifts mechanism. -/
structure DualLiftBridge (Lift Plus Minus Bulk Obs : Type*) where
  dual : Lift → Lift
  plus : Lift → Plus
  minus : Lift → Minus
  penrosePlus : Plus → Bulk
  penroseMinus : Minus → Bulk
  reverse : Bulk → Bulk
  observe : Lift → Obs
  dual_involutive : ∀ x, dual (dual x) = x
  reverse_involutive : ∀ b, reverse (reverse b) = b
  penrose_intertwines : ∀ x,
    penroseMinus (minus (dual x)) = reverse (penrosePlus (plus x))
  observable_invariant : ∀ x, observe (dual x) = observe x

namespace DualLiftBridge

variable {Lift Plus Minus Bulk Obs : Type*}
    (B : DualLiftBridge Lift Plus Minus Bulk Obs)

/-- The two representatives in a duality orbit have the same observable value. -/
theorem dual_same_observable (x : Lift) :
    B.observe (B.dual x) = B.observe x :=
  B.observable_invariant x

/-- Applying the diagonal duality twice returns the original lifted datum. -/
theorem dual_orbit_closes (x : Lift) :
    B.dual (B.dual x) = x :=
  B.dual_involutive x

/-- The defining googly square: the minus projection of the dual lift reconstructs
orientation reversal of the plus bulk field. -/
theorem googly_square (x : Lift) :
    B.penroseMinus (B.minus (B.dual x)) =
      B.reverse (B.penrosePlus (B.plus x)) :=
  B.penrose_intertwines x

/-- Applying the intertwining law to the dual lift shows that the opposite bulk
representative is also controlled by the original lift. -/
theorem googly_square_on_dual (x : Lift) :
    B.penroseMinus (B.minus (B.dual (B.dual x))) =
      B.reverse (B.penrosePlus (B.plus (B.dual x))) :=
  B.penrose_intertwines (B.dual x)

/-- After using involutivity upstairs, the preceding identity expresses the minus
bulk field of the original lift in terms of the plus field of its dual lift. -/
theorem minus_from_dual_plus (x : Lift) :
    B.penroseMinus (B.minus x) =
      B.reverse (B.penrosePlus (B.plus (B.dual x))) := by
  simpa [B.dual_involutive x] using B.penrose_intertwines (B.dual x)

/-- If bulk orientation reversal is itself involutive, the plus bulk field can be
recovered by reversing the minus bulk field of the dual representative. -/
theorem plus_from_dual_minus (x : Lift) :
    B.penrosePlus (B.plus x) =
      B.reverse (B.penroseMinus (B.minus (B.dual x))) := by
  rw [B.penrose_intertwines x, B.reverse_involutive]

end DualLiftBridge

/-- A minimal field-level Penrose commuting square independent of the choice of
lifted observable algebra.  This is the exact analytic theorem still to be supplied
for the ambient `epsilon` duality; the Lean result proves only its categorical
consequences. -/
structure PenroseDualitySquare (Tw DualTw Bulk : Type*) where
  toDual : Tw → DualTw
  penrose : Tw → Bulk
  dualPenrose : DualTw → Bulk
  reverse : Bulk → Bulk
  intertwines : ∀ z, dualPenrose (toDual z) = reverse (penrose z)

namespace PenroseDualitySquare

variable {Tw DualTw Bulk : Type*} (S : PenroseDualitySquare Tw DualTw Bulk)

/-- The abstract Penrose/orientation commuting square. -/
theorem commutes (z : Tw) :
    S.dualPenrose (S.toDual z) = S.reverse (S.penrose z) :=
  S.intertwines z

end PenroseDualitySquare

end GppAmbientFourPenroseIntertwiner
