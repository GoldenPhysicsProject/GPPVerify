import Mathlib.Tactic

/-!
# Orientation reversal alone cannot solve the nonlinear googly problem

Orientation reversal exchanges the names of the self-dual and anti-self-dual Weyl
components, but it does not manufacture an independent missing component.  Thus a
purely chiral field remains purely chiral after orientation reversal (with the opposite
label).  In particular, pairing a self-dual geometry with the same geometry viewed with
opposite orientation is not by itself a construction of a generic non-self-dual geometry.

This elementary observation is important for the googly programme: the split-signature
Penrose/Fourier/orientation square can close the linear representation problem, but the
nonlinear googly problem still requires a mechanism that permits both interacting chiral
components to be simultaneously nonzero.
-/

namespace GppOrientationOnlyGooglyNoGo

/-- Abstract chiral decomposition `(plus, minus)`. -/
structure ChiralPair (A : Type*) where
  plus : A
  minus : A
  deriving DecidableEq

/-- Orientation reversal swaps which component is called self-dual and anti-self-dual. -/
def reverseOrientation {A : Type*} (W : ChiralPair A) : ChiralPair A :=
  ⟨W.minus, W.plus⟩

/-- Orientation reversal is an involution. -/
theorem reverseOrientation_involutive {A : Type*} (W : ChiralPair A) :
    reverseOrientation (reverseOrientation W) = W := by
  cases W
  rfl

/-- A purely plus-chiral field remains purely chiral after orientation reversal: it
becomes purely minus-chiral, not a field with two independent components. -/
theorem pure_plus_stays_pure
    {A : Type*} [Zero A] (a : A) :
    reverseOrientation (ChiralPair.mk a 0) = ChiralPair.mk 0 a := by
  rfl

/-- Likewise a purely minus-chiral field becomes purely plus-chiral. -/
theorem pure_minus_stays_pure
    {A : Type*} [Zero A] (a : A) :
    reverseOrientation (ChiralPair.mk 0 a) = ChiralPair.mk a 0 := by
  rfl

/-- If `a` and `b` are both nonzero, a generic two-chirality field `(a,b)` cannot be
obtained by merely reversing the orientation of the purely chiral field `(a,0)`. -/
theorem generic_pair_not_from_reversing_pure_plus
    {A : Type*} [Zero A]
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    reverseOrientation (ChiralPair.mk a 0) ≠ ChiralPair.mk a b := by
  intro h
  have hp := congrArg ChiralPair.plus h
  simp [reverseOrientation] at hp
  exact ha hp.symm

/-- Nor can a generic pair arise by retaining the original pure field itself. -/
theorem generic_pair_not_pure_plus
    {A : Type*} [Zero A]
    (a b : A) (hb : b ≠ 0) :
    ChiralPair.mk a 0 ≠ ChiralPair.mk a b := by
  intro h
  have hm := congrArg ChiralPair.minus h
  simp at hm
  exact hb hm.symm

/-- Therefore the two-element orientation orbit of a nonzero purely chiral field contains
only the two pure chiral labelings.  It does not contain a generic field with both
components nonzero. -/
theorem orientation_orbit_of_pure_excludes_generic
    {A : Type*} [Zero A]
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    ChiralPair.mk a b ≠ ChiralPair.mk a 0 ∧
    ChiralPair.mk a b ≠ reverseOrientation (ChiralPair.mk a 0) := by
  constructor
  · exact (generic_pair_not_pure_plus a b hb).symm
  · exact (generic_pair_not_from_reversing_pure_plus a b ha hb).symm

end GppOrientationOnlyGooglyNoGo
