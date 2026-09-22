import Mathlib.Tactic

/-!
# Spin^c diagonal-center core: charged spinors already use a spacetime/gauge Z2 quotient

The global structure group for a charged spinor is naturally of Spin^c type,

    Spin^c(n) = (Spin(n) x U(1)) / {(+1,+1),(-1,-1)}.

The crucial finite core is a diagonal Z2 quotient: the nontrivial spin-cover center and the
pi gauge phase are identified together.  A representation descends through the quotient
only if their two central signs multiply to +1.

This file formalizes exactly that sign condition.  It is potentially important for the GPP
orientation programme because the diagonal quotient is not an invented algebraic trick: it
is the natural global structure of charged spinors.  However the spin-cover center `-1`
means a 2pi spin rotation/deck sign, NOT by itself the project's microscopic time arrow.
Connecting a Pin/time-orientation lift to this center is a separate theorem target.
-/

namespace GppSpinCChargeParityCore

/-- A binary central sign. -/
def zsign (b : Bool) : ℤ := if b then -1 else 1

/-- Descent through the diagonal center means the product action is trivial. -/
def descendsDiagonal (spin gauge : Bool) : Prop :=
  zsign spin * zsign gauge = 1

/-- The diagonal quotient condition holds exactly when the two central signs agree. -/
theorem descendsDiagonal_iff_equal (spin gauge : Bool) :
    descendsDiagonal spin gauge ↔ spin = gauge := by
  cases spin <;> cases gauge <;> native_decide

/-- The nontrivial diagonal element `(-1,-1)` acts trivially. -/
theorem minus_minus_trivial : descendsDiagonal true true := by
  native_decide

/-- Either one-sided center action fails the descent condition. -/
theorem one_sided_centers_nontrivial :
    ¬ descendsDiagonal true false ∧ ¬ descendsDiagonal false true := by
  native_decide

/-- If the spin-center acts as fermion parity `-1`, descent forces the U(1) pi-phase to act
    as `-1` too. -/
theorem fermionic_spin_parity_forces_odd_gauge_center
    (gauge : Bool) (h : descendsDiagonal true gauge) : gauge = true := by
  exact (descendsDiagonal_iff_equal true gauge).1 h |>.symm

/-- Conversely a bosonic/trivial spin-center action requires a trivial pi gauge phase in a
    representation descending through this particular diagonal quotient. -/
theorem trivial_spin_parity_forces_even_gauge_center
    (gauge : Bool) (h : descendsDiagonal false gauge) : gauge = false := by
  exact (descendsDiagonal_iff_equal false gauge).1 h |>.symm

end GppSpinCChargeParityCore
