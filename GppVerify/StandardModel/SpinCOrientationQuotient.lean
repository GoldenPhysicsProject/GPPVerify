import Mathlib.Tactic

/-!
# Spin^c orientation quotient and the 3(B-L) arithmetic core

Finite algebra accompanying Daniel Toupin,
"Which Way Is Forward?", v16.

This file formalizes only the discrete/algebraic layer used in the paper:

* the diagonal central sign (-1,-1) acts trivially on a charged spinor;
* the determinant/vector phase z^2 is invariant under z -> -z;
* X = 3(B-L) is odd on every SM fermion once one right-handed neutrino
  is included, while the Higgs is even;
* the SU(3)^2 X, SU(2)^2 X, gravitational-X, X^3,
  Y^2 X and Y X^2 anomaly sums vanish for one generation.

It does NOT formalize principal Spin^c bundles, anomaly descent, path integrals,
or identify the eight-dimensional normal-plane connection with B-L.
-/

namespace GppSpinCOrientationQuotient

/-- Central spin sign times central U(1) sign. -/
def diagonalCentralSign (spinSign gaugeSign : ℤ) : ℤ :=
  spinSign * gaugeSign

/-- The diagonal (-1,-1) acts trivially. -/
theorem diagonal_minus_minus_trivial :
    diagonalCentralSign (-1) (-1) = 1 := by
  norm_num [diagonalCentralSign]

/-- The determinant/vector phase cannot distinguish the two square-root lifts. -/
theorem square_phase_deck_invariant (z : ℂ) :
    (-z)^2 = z^2 := by
  ring

/-- Physical X=3(B-L) charges for one generation plus one right-handed neutrino. -/
def xQL : ℤ := 1
def xuR : ℤ := 1
def xdR : ℤ := 1
def xLL : ℤ := -3
def xeR : ℤ := -3
def xnR : ℤ := -3
def xH  : ℤ := 0

/-- Every fermionic X charge is odd. -/
theorem bl_fermion_charges_odd :
    Odd xQL ∧ Odd xuR ∧ Odd xdR ∧ Odd xLL ∧ Odd xeR ∧ Odd xnR := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [xQL, xuR, xdR, xLL, xeR, xnR] <;> decide

/-- The Higgs X charge is even. -/
theorem bl_higgs_charge_even : Even xH := by
  simp only [xH]; decide

/-!
For anomaly sums it is convenient to use only left-handed Weyl fields
(Q, u^c, d^c, L, e^c, N^c). Their X charges are
(1,-1,-1,-3,3,3), with multiplicities (6,3,3,2,1,1).
-/

def xQ  : ℤ := 1
def xuC : ℤ := -1
def xdC : ℤ := -1
def xL  : ℤ := -3
def xeC : ℤ := 3
def xnC : ℤ := 3

/-- SU(3)^2 U(1)_X anomaly numerator, up to the common Dynkin-index factor. -/
theorem su3_sq_x_anomaly_zero :
    2*xQ + xuC + xdC = 0 := by
  norm_num [xQ, xuC, xdC]

/-- SU(2)^2 U(1)_X anomaly numerator, up to the common Dynkin-index factor. -/
theorem su2_sq_x_anomaly_zero :
    3*xQ + xL = 0 := by
  norm_num [xQ, xL]

/-- Mixed gravitational-U(1)_X anomaly vanishes. -/
theorem gravitational_x_anomaly_zero :
    6*xQ + 3*xuC + 3*xdC + 2*xL + xeC + xnC = 0 := by
  norm_num [xQ, xuC, xdC, xL, xeC, xnC]

/-- Cubic U(1)_X anomaly vanishes. -/
theorem x_cubic_anomaly_zero :
    6*xQ^3 + 3*xuC^3 + 3*xdC^3 + 2*xL^3 + xeC^3 + xnC^3 = 0 := by
  norm_num [xQ, xuC, xdC, xL, xeC, xnC]

/-- Hypercharges of the same left-handed Weyl fields. -/
def yQ  : ℚ := 1/6
def yuC : ℚ := -2/3
def ydC : ℚ := 1/3
def yL  : ℚ := -1/2
def yeC : ℚ := 1
def ynC : ℚ := 0

/-- U(1)_Y^2 U(1)_X anomaly vanishes. -/
theorem y_sq_x_anomaly_zero :
    6*yQ^2*(xQ : ℚ) +
    3*yuC^2*(xuC : ℚ) +
    3*ydC^2*(xdC : ℚ) +
    2*yL^2*(xL : ℚ) +
    yeC^2*(xeC : ℚ) +
    ynC^2*(xnC : ℚ) = 0 := by
  norm_num [yQ, yuC, ydC, yL, yeC, ynC, xQ, xuC, xdC, xL, xeC, xnC]

/-- U(1)_Y U(1)_X^2 anomaly vanishes. -/
theorem y_x_sq_anomaly_zero :
    6*yQ*(xQ : ℚ)^2 +
    3*yuC*(xuC : ℚ)^2 +
    3*ydC*(xdC : ℚ)^2 +
    2*yL*(xL : ℚ)^2 +
    yeC*(xeC : ℚ)^2 +
    ynC*(xnC : ℚ)^2 = 0 := by
  norm_num [yQ, yuC, ydC, yL, yeC, ynC, xQ, xuC, xdC, xL, xeC, xnC]

/-- Residual order-two deck parity.  Using natAbs makes the definition independent
of the sign convention for the Abelian charge. -/
def deckParity (X : ℤ) : ℤ := (-1 : ℤ) ^ X.natAbs

/-- Charge conjugation X -> -X leaves the residual deck parity unchanged. -/
theorem deckParity_charge_conjugation_even (X : ℤ) :
    deckParity (-X) = deckParity X := by
  simp [deckParity]

/-- A scalar of X-charge 6 has even charge, so its vacuum can preserve the X-parity subgroup. -/
theorem majorana_scalar_charge_even : Even (6 : ℤ) := by
  norm_num [Even]

end GppSpinCOrientationQuotient
