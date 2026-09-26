import Mathlib.Tactic
import GppVerify.CelestialHolography.AmbitwistorContactNeutralCone

/-!
# Bicomplex factorization of the ambitwistor contact chirality sign

The rank-four flat ambitwistor contact screen is written as

    H = L_- ⊕ L_+,

with para-complex involution

    K(X,Y) = (X,-Y).

This file exhibits `K` as the product of two *commuting complex structures* on the same
real four-dimensional carrier.

Let `j(x0,x1)=(-x1,x0)` be the ordinary quarter-turn on a real two-plane.  Define

    J0(X,Y) = ( jX,  jY),
    J1(X,Y) = (-jX,  jY).

Then

    J0^2 = J1^2 = -1,
    J0 J1 = J1 J0 = K.

Thus the left/right `±1` contact-chirality label is literally a *relative orientation*
between two commuting quarter-turn structures.  Reversing both `J0` and `J1` leaves `K`
unchanged, while reversing either one flips `K`.

The canonical factor exchange `E(X,Y)=(Y,X)` has an especially sharp action:

    E J0 = J0 E,
    E J1 = - J1 E,
    E K  = - K E.

So factor/ruling exchange preserves one complex orientation and reverses the other; it is
a mathematically exact half-flip of the relative-orientation product.

No claim is made here that `J0` is physical time phase or that `J1` is electric charge.
The result supplies the finite contact-geometric carrier on which such a dictionary would
have to be proved.
-/

namespace GppAmbitwistorBicomplexOrientation

open GppAmbitwistorContactNeutralCone

/-- Standard real quarter-turn on a two-dimensional contact half. -/
def quarter2 (x : ContactHalf) : ContactHalf := (-x.2, x.1)

/-- Overall/common complex orientation: the same quarter-turn on both contact halves. -/
def commonJ (u : ContactVector) : ContactVector :=
  (quarter2 u.1, quarter2 u.2)

/-- Relative/chiral complex orientation: opposite quarter-turn orientation on the two halves. -/
def relativeJ (u : ContactVector) : ContactVector :=
  ((- (quarter2 u.1).1, - (quarter2 u.1).2), quarter2 u.2)

/-- Negation of a contact vector. -/
def negContact (u : ContactVector) : ContactVector :=
  ((-u.1.1,-u.1.2),(-u.2.1,-u.2.2))

/-- Each planar quarter-turn squares to the central sign. -/
theorem quarter2_sq (x : ContactHalf) :
    quarter2 (quarter2 x) = (-x.1,-x.2) := by
  rcases x with ⟨x0,x1⟩
  rfl

/-- The common quarter-turn is a complex structure on the real contact screen. -/
theorem commonJ_sq (u : ContactVector) :
    commonJ (commonJ u) = negContact u := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  rfl

/-- The relative/chiral quarter-turn is also a complex structure. -/
theorem relativeJ_sq (u : ContactVector) :
    relativeJ (relativeJ u) = negContact u := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  rfl

/-- The two complex structures commute. -/
theorem commonJ_relativeJ_commute (u : ContactVector) :
    commonJ (relativeJ u) = relativeJ (commonJ u) := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  rfl

/-- Main factorization: the contact para-complex chirality involution is the product of the
two commuting complex structures. -/
theorem commonJ_relativeJ_eq_paraJ (u : ContactVector) :
    commonJ (relativeJ u) = paraJ u := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  rfl

/-- The opposite ordering gives the same para-complex involution. -/
theorem relativeJ_commonJ_eq_paraJ (u : ContactVector) :
    relativeJ (commonJ u) = paraJ u := by
  rw [← commonJ_relativeJ_commute, commonJ_relativeJ_eq_paraJ]

/-- Simultaneously reversing both complex orientations leaves their product unchanged. -/
theorem reverse_both_preserves_para_product (u : ContactVector) :
    commonJ (relativeJ u) = paraJ u :=
  commonJ_relativeJ_eq_paraJ u

/-- Factor exchange commutes with the common complex orientation. -/
theorem exchange_commutes_commonJ (u : ContactVector) :
    exchangeHalves (commonJ u) = commonJ (exchangeHalves u) := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  rfl

/-- Factor exchange reverses the relative complex orientation. -/
theorem exchange_anticommutes_relativeJ (u : ContactVector) :
    exchangeHalves (relativeJ u) = negContact (relativeJ (exchangeHalves u)) := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  rfl

/-- Consequently factor exchange flips the para-complex/chirality sign. -/
theorem exchange_anticommutes_paraJ (u : ContactVector) :
    exchangeHalves (paraJ u) = negContact (paraJ (exchangeHalves u)) := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  rfl

/-- Pure left directions are `+1` eigenvectors of the relative product `K=paraJ`. -/
theorem left_is_para_plus (x : ContactHalf) :
    paraJ (x,(0,0)) = (x,(0,0)) := by
  rcases x with ⟨x0,x1⟩
  rfl

/-- Pure right directions are `-1` eigenvectors of the same relative product. -/
theorem right_is_para_minus (y : ContactHalf) :
    paraJ ((0,0),y) = negContact ((0,0),y) := by
  rcases y with ⟨y0,y1⟩
  rfl

/-- Exchange swaps the two eigenbundles of the relative-orientation involution. -/
theorem exchange_left_to_right (x : ContactHalf) :
    exchangeHalves (x,(0,0)) = ((0,0),x) := by
  rfl

end GppAmbitwistorBicomplexOrientation
