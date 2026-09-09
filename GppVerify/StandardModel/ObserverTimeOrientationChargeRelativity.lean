import Mathlib.Tactic
import GppVerify.StandardModel.ChargedCARComplexOrientationNoGo
import GppVerify.StandardModel.ChargedCARChargeTimeComplexDictionary

/-!
# Fixed-standard time orientation versus complete time reversal

The charged-CAR structure gives a precise version of the distinction between the coordinate
/time parameter used by an observer and the microscopic orientation carried by the dynamics.

Let

    I  = original U(1)/phase-space complex structure,
    q  = sgn b,
    J  = I q,

so physical particle/antiparticle charge is the relative complex orientation `q=-I J`.

There are two mathematically different ways to reverse the temporal description.

(1) FIXED-STANDARD ORIENTATION REVERSAL.
    Reparameterize the same one-parameter dynamics by `t'=-t` while keeping the observer's
    original complex/charge standard `I` fixed.  The infinitesimal generator changes sign,

        b -> -b,

    hence

        q=sgn b -> -q,
        J=I q   -> -J.

    Thus relative charge flips.  This is the precise version of: "if I keep my charge
    standard fixed but read the microscopic temporal orientation the other way, matter is
    read as antimatter."

(2) COMPLETE ANTI-LINEAR TIME REVERSAL.
    The physical time-reversal map is anti-linear.  It reverses the scalar complex structure
    as well as the positive-energy complex structure,

        I -> -I,
        J -> -J,

    and therefore leaves their relative product `q=-I J` unchanged.

So the observer-relative half comparison and the complete time-reversed theory are not the
same operation.  The thermodynamic arrow does not enter this algebra.
-/

namespace GppObserverTimeOrientationChargeRelativity

open GppChargedCARComplexOrientationNoGo
open GppChargedCARChargeTimeComplexDictionary

/-- Algebraic fixed-standard reversal: keep I, reverse q and therefore reverse J=Iq. -/
def fixedStandardReverseQ : M2 := -qSign
def fixedStandardReverseJ : M2 := -energyJ

/-- With the phase standard held fixed, reversing the dynamical sign reverses relative charge. -/
theorem fixed_standard_reverse_flips_relative_charge :
    -(phaseI * fixedStandardReverseJ) = fixedStandardReverseQ := by
  simp [fixedStandardReverseJ, fixedStandardReverseQ]
  rw [← qSign_eq_relative_orientation]
  simp

/-- The positive-energy complex structure really changes sign under the fixed-standard
    orientation reversal. -/
theorem fixed_standard_reverse_J_is_negative :
    fixedStandardReverseJ = -energyJ := by rfl

/-- The relative charge sign really changes under the fixed-standard orientation reversal. -/
theorem fixed_standard_reverse_q_is_negative :
    fixedStandardReverseQ = -qSign := by rfl

/-- Complete anti-linear T reverses both absolute complex orientations but preserves q. -/
theorem complete_time_reversal_preserves_relative_charge (v : V2) :
    timeT (phaseI *ᵥ v) = (-phaseI) *ᵥ timeT v ∧
    timeT (energyJ *ᵥ v) = (-energyJ) *ᵥ timeT v ∧
    timeT (qSign *ᵥ v) = qSign *ᵥ timeT v := by
  exact ⟨T_reverses_phaseI v, T_reverses_energyJ v, T_preserves_qSign v⟩

/-- Charge reversal is the complementary half flip: it reverses I, preserves J, and hence
    reverses the same relative charge q. -/
theorem charge_reversal_is_other_half_flip (v : V2) :
    chargeC (phaseI *ᵥ v) = (-phaseI) *ᵥ chargeC v ∧
    chargeC (energyJ *ᵥ v) = energyJ *ᵥ chargeC v ∧
    chargeC (qSign *ᵥ v) = (-qSign) *ᵥ chargeC v := by
  exact ⟨C_reverses_phaseI v, C_preserves_energyJ v, C_flips_qSign v⟩

/-- Capstone: either one-orientation half flip reverses q, while the complete two-orientation
    anti-linear time reversal preserves q. -/
theorem observer_relative_orientation_capstone (v : V2) :
    fixedStandardReverseQ = -qSign ∧
    chargeC (qSign *ᵥ v) = (-qSign) *ᵥ chargeC v ∧
    timeT (qSign *ᵥ v) = qSign *ᵥ timeT v := by
  exact ⟨rfl, C_flips_qSign v, T_preserves_qSign v⟩

end GppObserverTimeOrientationChargeRelativity
