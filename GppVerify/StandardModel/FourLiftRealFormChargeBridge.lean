import Mathlib.Tactic
import GppVerify.StandardModel.OrientationComplexStructureDoubleCover

/-!
# Four-lift real form and two-sector charge bridge

This file records the finite correction used in Version 21 of
"Which Way Is Forward?".

The simultaneous reversal `diagReverse` is not identified with the central
scalar `-1`.  Relative to the microscopic complex structure `Iq`,
`diagReverse` is an involutive real structure.  Its fixed carrier has the
paired form `(a,b,b,a)`.

On that fixed carrier the two microscopic half flips agree, and the surviving
relational grading `chi` is intertwined with the standard two-sector normal
form `diag(+1,-1)`.

This is finite linear algebra only.  It does not identify full QFT charge
conjugation with Wigner time reversal.
-/

namespace GppFourLiftRealFormChargeBridge

open GppFourOrientationGaugeProjection
open GppOrientationComplexStructureDoubleCover

abbrev Pair2 := ℂ × ℂ

/-- Coordinates on the diagonal fixed carrier. -/
def fixedCoords (v : Orientation4) : Pair2 := (v.1, v.2.1)

/-- Canonical embedding of two charge-sector amplitudes into the fixed carrier. -/
def embedFixed (z : Pair2) : Orientation4 := physicalLift z.1 z.2

/-- Standard two-sector charge grading. -/
def pairCharge (z : Pair2) : Pair2 := (z.1, -z.2)

/-- Standard two-sector exchange. -/
def pairSwap (z : Pair2) : Pair2 := (z.2, z.1)

/-- The canonical embedding lands in the fixed carrier. -/
theorem embedFixed_is_fixed (z : Pair2) :
    diagReverse (embedFixed z) = embedFixed z := by
  rcases z with ⟨a,b⟩
  rfl

/-- Every fixed vector is recovered from its two coordinates. -/
theorem embed_fixedCoords_of_fixed (v : Orientation4)
    (h : diagReverse v = v) :
    embedFixed (fixedCoords v) = v := by
  obtain ⟨a,b,hv⟩ := diag_even_has_paired_form v h
  subst v
  rfl

/-- The microscopic complex structure maps the fixed carrier to the odd complement. -/
theorem Iq_fixed_to_odd (v : Orientation4)
    (h : diagReverse v = v) :
    diagReverse (Iq v) = - Iq v := by
  exact (individual_arrows_do_not_descend v h).1

/-- The two half flips induce exactly the same map on the fixed carrier. -/
theorem half_flips_agree_on_fixed (v : Orientation4)
    (h : diagReverse v = v) :
    chargeFlip v = temporalFlip v := by
  obtain ⟨a,b,hv⟩ := diag_even_has_paired_form v h
  subst v
  rfl

/-- Either half flip preserves the fixed carrier. -/
theorem half_flips_preserve_fixed (v : Orientation4)
    (h : diagReverse v = v) :
    diagReverse (chargeFlip v) = chargeFlip v ∧
    diagReverse (temporalFlip v) = temporalFlip v := by
  obtain ⟨a,b,hv⟩ := diag_even_has_paired_form v h
  subst v
  exact ⟨rfl,rfl⟩

/-- The relational grading is exactly the standard two-sector charge normal form. -/
theorem chi_intertwines_pairCharge (z : Pair2) :
    fixedCoords (chi (embedFixed z)) = pairCharge z := by
  rcases z with ⟨a,b⟩
  simp [fixedCoords, embedFixed, pairCharge, physicalLift, chi]

/-- Either microscopic half flip is the standard two-sector exchange downstairs. -/
theorem half_flip_intertwines_pairSwap (z : Pair2) :
    fixedCoords (chargeFlip (embedFixed z)) = pairSwap z ∧
    fixedCoords (temporalFlip (embedFixed z)) = pairSwap z := by
  rcases z with ⟨a,b⟩
  exact ⟨rfl,rfl⟩

/-- The diagonal fixed carrier retains both relational charge sectors. -/
theorem fixed_charge_eigenvectors :
    pairCharge (1,0) = (1,0) ∧
    pairCharge (0,1) = -(0,1) := by
  norm_num [pairCharge]

/-- The diagonal reversal is not the central scalar minus identity. -/
theorem diagReverse_not_scalar_neg :
    diagReverse matterLift ≠ -matterLift := by
  norm_num [diagReverse, matterLift]

/-- Capstone: fixed-carrier coordinates, charge grading, and the two half flips. -/
theorem real_form_charge_capstone (a b : ℂ) :
    diagReverse (embedFixed (a,b)) = embedFixed (a,b) ∧
    fixedCoords (chi (embedFixed (a,b))) = pairCharge (a,b) ∧
    fixedCoords (chargeFlip (embedFixed (a,b))) = pairSwap (a,b) ∧
    fixedCoords (temporalFlip (embedFixed (a,b))) = pairSwap (a,b) := by
  exact ⟨rfl,
    chi_intertwines_pairCharge (a,b),
    (half_flip_intertwines_pairSwap (a,b)).1,
    (half_flip_intertwines_pairSwap (a,b)).2⟩

end GppFourLiftRealFormChargeBridge
