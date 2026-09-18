import Mathlib.Tactic
import GppVerify.CelestialHolography.KleinSpinorIncidence

/-!
# Relative mass shell in a doubled Lorentz carrier

This module formalizes the elementary quadratic algebra behind the doubled
3+1 null-parent reduction.  A four-vector is represented by the existing
coordinate carrier V4.  We choose the space-positive convention

  Q(t,x,y,z) = x^2 + y^2 + z^2 - t^2.

For two Lorentz vectors p1,p2, define the unnormalized sum and difference

  s = p1+p2,   d = p1-p2.

Then

  Q(s) + Q(d) = 2 Q(p1) + 2 Q(p2).

Hence a null point of the doubled quadratic form, Q(p1)+Q(p2)=0, has
Q(s)=-Q(d).  If the relative difference is spacelike, the sum is timelike
with equal invariant magnitude.

The canonical quarter-turn J(p1,p2)=(p2,-p1) acts in sum/difference
coordinates as (s,d)->(-d,s), displaying the exact Z4 structure.

No physical identification of Q(d)/2 with observed rest mass is assumed here;
that is the dictionary supplied by the continuum Routh reduction in the paper.
-/

namespace GppDoubledLorentzRelativeMass

open GppTwistorAnnihilatorIncidence

/-- Space-positive Lorentz quadratic form on coordinates (t,x,y,z). -/
def lorentzQ (p : V4) : ℝ :=
  p.2.1^2 + p.2.2.1^2 + p.2.2.2^2 - p.1^2

/-- Componentwise sum. -/
def add4 (x y : V4) : V4 :=
  (x.1+y.1, x.2.1+y.2.1, x.2.2.1+y.2.2.1, x.2.2.2+y.2.2.2)

/-- Componentwise difference. -/
def sub4 (x y : V4) : V4 :=
  (x.1-y.1, x.2.1-y.2.1, x.2.2.1-y.2.2.1, x.2.2.2-y.2.2.2)

/-- Componentwise negation. -/
def neg4 (x : V4) : V4 :=
  (-x.1,-x.2.1,-x.2.2.1,-x.2.2.2)

/-- Parallelogram identity for the Lorentz quadratic form. -/
theorem lorentzQ_parallelogram (p1 p2 : V4) :
    lorentzQ (add4 p1 p2) + lorentzQ (sub4 p1 p2) =
      2 * lorentzQ p1 + 2 * lorentzQ p2 := by
  rcases p1 with ⟨t1,x1,y1,z1⟩
  rcases p2 with ⟨t2,x2,y2,z2⟩
  simp [lorentzQ, add4, sub4]
  ring

/-- On the doubled null cone, sum and relative difference have opposite norm. -/
theorem doubled_null_sum_eq_neg_difference
    (p1 p2 : V4)
    (hnull : lorentzQ p1 + lorentzQ p2 = 0) :
    lorentzQ (add4 p1 p2) = - lorentzQ (sub4 p1 p2) := by
  have h := lorentzQ_parallelogram p1 p2
  linarith

abbrev DoubledMomentum := V4 × V4

/-- Canonical order-four exchange on the two Lorentz copies. -/
def quarterTurn (u : DoubledMomentum) : DoubledMomentum :=
  (u.2, neg4 u.1)

/-- Four applications return the original doubled momentum. -/
theorem quarterTurn_four (u : DoubledMomentum) :
    quarterTurn (quarterTurn (quarterTurn (quarterTurn u))) = u := by
  rcases u with ⟨⟨a,b,c,d⟩,⟨e,f,g,h⟩⟩
  simp [quarterTurn, neg4]

/-- Under the quarter-turn, the sum variable becomes minus the old difference. -/
theorem add4_quarterTurn (u : DoubledMomentum) :
    add4 (quarterTurn u).1 (quarterTurn u).2 =
      neg4 (sub4 u.1 u.2) := by
  rcases u with ⟨⟨a,b,c,d⟩,⟨e,f,g,h⟩⟩
  simp [quarterTurn, add4, sub4, neg4]
  ring

/-- Under the quarter-turn, the difference variable becomes the old sum. -/
theorem sub4_quarterTurn (u : DoubledMomentum) :
    sub4 (quarterTurn u).1 (quarterTurn u).2 =
      add4 u.1 u.2 := by
  rcases u with ⟨⟨a,b,c,d⟩,⟨e,f,g,h⟩⟩
  simp [quarterTurn, add4, sub4, neg4]
  ring

/-- The Lorentz norm is even under componentwise negation. -/
theorem lorentzQ_neg4 (p : V4) :
    lorentzQ (neg4 p) = lorentzQ p := by
  rcases p with ⟨t,x,y,z⟩
  simp [lorentzQ, neg4]
  ring

/-- The quarter-turn swaps the sum and difference Lorentz norms. -/
theorem quarterTurn_swaps_sum_difference_norms (u : DoubledMomentum) :
    lorentzQ (add4 (quarterTurn u).1 (quarterTurn u).2) =
      lorentzQ (sub4 u.1 u.2) ∧
    lorentzQ (sub4 (quarterTurn u).1 (quarterTurn u).2) =
      lorentzQ (add4 u.1 u.2) := by
  rw [add4_quarterTurn, sub4_quarterTurn, lorentzQ_neg4]
  exact ⟨rfl,rfl⟩

end GppDoubledLorentzRelativeMass
