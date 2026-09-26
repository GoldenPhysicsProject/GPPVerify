import Mathlib.Tactic
import GppVerify.CelestialHolography.KleinPinOrderFourBlock

/-!
# Doubled Lorentz carrier and its canonical quarter-turn

For two copies of the same four-component carrier, the map

  J(x,y) = (y,-x)

is a canonical order-four exchange.  Its square is the diagonal central sign and its
fourth power is identity.  The diagonal and anti-diagonal four-planes are exchanged.

This file is deliberately metric-free: it formalizes only the exact Z4 algebra on
the doubled carrier.  Interpreting the two copies as Lorentzian 3+1 spaces and the
direct sum as a real (6,2) carrier requires a separately chosen bilinear form.
-/

namespace GppDoubledLorentzQuarterTurn

open GppKleinSpinorIncidence
open GppTwistorAnnihilatorIncidence

abbrev DoubledV4 := V4 × V4

/-- Componentwise negation. -/
def neg4 (x : V4) : V4 :=
  (-x.1,-x.2.1,-x.2.2.1,-x.2.2.2)

/-- Canonical exchange with one relative sign. -/
def quarterTurn8 (u : DoubledV4) : DoubledV4 :=
  (u.2, neg4 u.1)

/-- Two turns give the diagonal central sign. -/
theorem quarterTurn8_sq (u : DoubledV4) :
    quarterTurn8 (quarterTurn8 u) = (neg4 u.1, neg4 u.2) := by
  rcases u with ⟨⟨a,b,c,d⟩,⟨e,f,g,h⟩⟩
  rfl

/-- Four turns close exactly. -/
theorem quarterTurn8_four (u : DoubledV4) :
    quarterTurn8 (quarterTurn8 (quarterTurn8 (quarterTurn8 u))) = u := by
  rcases u with ⟨⟨a,b,c,d⟩,⟨e,f,g,h⟩⟩
  simp [quarterTurn8, neg4]

/-- Diagonal embedding of one four-component sector. -/
def diag4 (x : V4) : DoubledV4 := (x,x)

/-- Anti-diagonal embedding. -/
def antiDiag4 (x : V4) : DoubledV4 := (x,neg4 x)

/-- One quarter-turn sends the diagonal sector to the anti-diagonal sector. -/
theorem quarterTurn8_diag (x : V4) :
    quarterTurn8 (diag4 x) = antiDiag4 x := by
  rcases x with ⟨a,b,c,d⟩
  rfl

/-- A second quarter-turn sends the anti-diagonal sector to minus the diagonal. -/
theorem quarterTurn8_antiDiag (x : V4) :
    quarterTurn8 (antiDiag4 x) = (neg4 x, neg4 x) := by
  rcases x with ⟨a,b,c,d⟩
  rfl

end GppDoubledLorentzQuarterTurn
