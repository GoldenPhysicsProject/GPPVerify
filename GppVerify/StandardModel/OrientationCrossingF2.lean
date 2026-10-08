import Mathlib.Tactic
import GppVerify.StandardModel.OrientationCliffordCore
import GppVerify.StandardModel.ComplementaryPairs
import GppVerify.CelestialHolography.CelestialCrossingGoldenSector

/-!
# Four lifts over F₂: complementary pairings, orientation flips, and crossing cusps

The four orientation labels (++),(+-),(-+),(--) form the affine set F₂².  Its
three nonzero translations are exactly the charge half flip, temporal half flip,
and simultaneous/deck reversal.  The three fixed-point-free involutions of a
four-element set are therefore not a second independent "three": after this
identification they are those same three translations.

Over F₂, P¹(F₂) is also a three-element set.  The already-formalized golden
crossing action is a 3-cycle on its cusps.  This file gives an explicit order-three
permutation matrix P on the four-lift carrier whose conjugation action cycles

  Rq -> Rt -> D -> Rq,

and an order-two matrix S that swaps Rq and Rt while fixing D.  P,S obey the
dihedral/S₃ relation S P S = P².

Only finite permutation/matrix algebra is proved.  No fermion-generation
identification is made.
-/

namespace GppOrientationCrossingF2

open Matrix
open GppOrientationCliffordCore
open GppComplementaryPairs
open GppCelestialCrossingGoldenSector

/-- The charge-half-flip partner map on the four lift labels
0=(++), 1=(+-), 2=(-+), 3=(--). -/
def rqPartner : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- The time-half-flip partner map. -/
def rtPartner : Fin 4 → Fin 4 := ![1, 0, 3, 2]

/-- The simultaneous/deck-reversal partner map. -/
def dPartner : Fin 4 → Fin 4 := ![3, 2, 1, 0]

/-- The three orientation partner maps exhaust the complementary pairings. -/
theorem complementary_pairings_are_orientation_flips :
    complementaryPairings = {rqPartner, rtPartner, dPartner} := by
  native_decide

/-- In particular the three orientation partner maps are pairwise distinct. -/
theorem orientation_partner_maps_distinct :
    rqPartner ≠ rtPartner ∧ rqPartner ≠ dPartner ∧ rtPartner ≠ dPartner := by
  native_decide

/-- Each nontrivial orientation translation is a fixed-point-free involution. -/
theorem orientation_partner_involutions :
    (∀ i, rqPartner (rqPartner i) = i) ∧ (∀ i, rqPartner i ≠ i) ∧
    (∀ i, rtPartner (rtPartner i) = i) ∧ (∀ i, rtPartner i ≠ i) ∧
    (∀ i, dPartner (dPartner i) = i) ∧ (∀ i, dPartner i ≠ i) := by
  native_decide

/-- Identify the three crossing cusps with the three nonzero orientation
translation directions. -/
def pairingOfCusp : CrossingCusp → (Fin 4 → Fin 4)
  | .infinity => rqPartner
  | .zero => rtPartner
  | .one => dPartner

/-- The golden crossing three-cycle is exactly Rq -> Rt -> D -> Rq
under the finite identification. -/
theorem crossing_cycle_is_orientation_cycle :
    pairingOfCusp (goldenCuspAction .infinity) = rtPartner ∧
    pairingOfCusp (goldenCuspAction .zero) = dPartner ∧
    pairingOfCusp (goldenCuspAction .one) = rqPartner := by
  decide

/-- Four-lift permutation implementing the mod-two golden map
(x,y) -> (y,x+y). -/
def P : M :=
  !![1,0,0,0;
     0,0,1,0;
     0,0,0,1;
     0,1,0,0]

/-- The transposition (x,y) -> (y,x). -/
def S : M :=
  !![1,0,0,0;
     0,0,1,0;
     0,1,0,0;
     0,0,0,1]

/-- The golden four-lift permutation has order three. -/
theorem P_order_three : P * P * P = (1 : M) := by
  decide

/-- The coordinate swap has order two. -/
theorem S_order_two : S * S = (1 : M) := by
  decide

/-- The two generators obey the S₃ relation S P S = P². -/
theorem S_P_S_eq_P_sq : S * P * S = P * P := by
  decide

/-- The three orientation translation matrices form the Klein four translation group. -/
theorem orientation_translation_V4 :
    Rq * Rq = 1 ∧ Rt * Rt = 1 ∧ D * D = 1 ∧
    Rq * Rt = D ∧ Rt * Rq = D := by
  decide

/-- Conjugation by P cycles the three nonzero orientation translations.  We write
the inverse as P², justified by P³=1. -/
theorem P_conjugation_cycle :
    P * Rq * (P * P) = Rt ∧
    P * Rt * (P * P) = D ∧
    P * D * (P * P) = Rq := by
  decide

/-- Conjugation by S fixes D and swaps the two half flips. -/
theorem S_conjugation_stabilizes_D :
    S * Rq * S = Rt ∧
    S * Rt * S = Rq ∧
    S * D * S = D := by
  decide

/-- Standard basis vector over the same Gaussian-integer carrier. -/
def basisLift (j : Fin 4) : Fin 4 → K :=
  fun i => if i = j then 1 else 0

/-- The matrix Rq acts on lift basis vectors exactly by rqPartner. -/
theorem Rq_basis_action (j : Fin 4) :
    Rq *ᵥ basisLift j = basisLift (rqPartner j) := by
  fin_cases j <;>
    funext i <;> fin_cases i <;>
    decide

/-- The matrix Rt acts on lift basis vectors exactly by rtPartner. -/
theorem Rt_basis_action (j : Fin 4) :
    Rt *ᵥ basisLift j = basisLift (rtPartner j) := by
  fin_cases j <;>
    funext i <;> fin_cases i <;>
    decide

/-- The matrix D acts on lift basis vectors exactly by dPartner. -/
theorem D_basis_action (j : Fin 4) :
    D *ᵥ basisLift j = basisLift (dPartner j) := by
  fin_cases j <;>
    funext i <;> fin_cases i <;>
    decide

/-- P fixes the (++ ) lift and cyclically permutes the other three lift basis
vectors. -/
theorem P_basis_cycle :
    P *ᵥ basisLift 0 = basisLift 0 ∧
    P *ᵥ basisLift 1 = basisLift 3 ∧
    P *ᵥ basisLift 3 = basisLift 2 ∧
    P *ᵥ basisLift 2 = basisLift 1 := by
  decide

end GppOrientationCrossingF2

#print axioms GppOrientationCrossingF2.complementary_pairings_are_orientation_flips
#print axioms GppOrientationCrossingF2.P_conjugation_cycle
#print axioms GppOrientationCrossingF2.S_conjugation_stabilizes_D
