import Mathlib.Tactic
import GppVerify.CelestialHolography.FlatInfinityCelestialFactorization

/-!
# Neutral contact-screen cone of the flat Lagrangian ambitwistor geometry

Flat projective ambitwistor space is the type-A Lagrangian-contact flag geometry
`P(T*P^3)`, equivalently the incidence hypersurface in `P^3 x P^{3*}`.  Its rank-four
contact hyperplane splits into two rank-two Lagrangian/Legendrian subspaces, corresponding
to the two projective factors.

At the finite linear-algebra level write a contact vector as a pair `(X,Y)` with
`X,Y in R^2`.  The Levi pairing between the two halves gives the alternating form

  L((X,Y),(X',Y')) = X.Y' - X'.Y.

The para-complex involution `K(X,Y)=(X,-Y)` then gives a symmetric neutral pairing

  g(u,v) = - L(u,Kv) = X.Y' + X'.Y,

with quadratic form

  g(u,u) = 2 X.Y.

Therefore the contact-null cone is exactly

  X.Y = 0.

This is the coordinate condition quoted in the standard Lagrangian-contact homogeneous
model: contact-null vectors are the pairs for which `Y^T X=0`.  In Penrose's TN41
adapted ambitwistor notation, the corresponding second-order strong-incidence condition
is `dZ.dW=0`.

This module proves the universal rank-two Lagrangian-contact algebra.  The geometric
identification of the abstract halves `(X,Y)` with the projectivized tangent components
of a particular ambitwistor chart is standard external Lagrangian-contact geometry and
is not encoded as a coordinate chart theorem here.
-/

namespace GppAmbitwistorContactNeutralCone

open GppFlatInfinityCelestialFactorization

abbrev ContactHalf := Spinor2
abbrev ContactVector := ContactHalf × ContactHalf

/-- Pairing between the two rank-two Lagrangian halves. -/
def halfPair (x y : ContactHalf) : ℝ := x.1*y.1 + x.2*y.2

/-- Levi/symplectic form on the rank-four contact screen. -/
def leviForm (u v : ContactVector) : ℝ :=
  halfPair u.1 v.2 - halfPair v.1 u.2

/-- Para-complex involution selecting the two Lagrangian halves. -/
def paraJ (u : ContactVector) : ContactVector := (u.1, (-u.2.1,-u.2.2))

/-- Symmetric split pairing canonically obtained from Levi form plus the Lagrangian
splitting, up to the overall contact-line scale. -/
def neutralPair (u v : ContactVector) : ℝ := - leviForm u (paraJ v)

/-- Its quadratic form. -/
def neutralQ (u : ContactVector) : ℝ := neutralPair u u

/-- The Levi form is alternating. -/
theorem leviForm_skew (u v : ContactVector) :
    leviForm u v = - leviForm v u := by
  simp [leviForm]
  ring

/-- Each chiral/Lagrangian half is Levi-isotropic. -/
theorem left_half_isotropic (x x' : ContactHalf) :
    leviForm (x,(0,0)) (x',(0,0)) = 0 := by
  simp [leviForm, halfPair]

/-- The opposite half is also Levi-isotropic. -/
theorem right_half_isotropic (y y' : ContactHalf) :
    leviForm ((0,0),y) ((0,0),y') = 0 := by
  simp [leviForm, halfPair]

/-- The para-complex operation squares to the identity. -/
theorem paraJ_sq (u : ContactVector) : paraJ (paraJ u) = u := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  rfl

/-- The neutral pairing is symmetric. -/
theorem neutralPair_symm (u v : ContactVector) :
    neutralPair u v = neutralPair v u := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  rcases v with ⟨⟨a0,a1⟩,⟨b0,b1⟩⟩
  simp [neutralPair, leviForm, paraJ, halfPair]
  ring

/-- Explicit cross-pairing formula. -/
theorem neutralPair_eq_cross_sum (u v : ContactVector) :
    neutralPair u v = halfPair u.1 v.2 + halfPair v.1 u.2 := by
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  rcases v with ⟨⟨a0,a1⟩,⟨b0,b1⟩⟩
  simp [neutralPair, leviForm, paraJ, halfPair]
  ring

/-- Main quadratic identity: the neutral norm is twice the pairing of the two halves. -/
theorem neutralQ_eq_twice_halfPair (u : ContactVector) :
    neutralQ u = 2 * halfPair u.1 u.2 := by
  rw [neutralQ, neutralPair_eq_cross_sum]
  ring

/-- Hence the contact-null cone is exactly `Y^T X = 0`. -/
theorem neutralQ_zero_iff_halfPair_zero (u : ContactVector) :
    neutralQ u = 0 ↔ halfPair u.1 u.2 = 0 := by
  rw [neutralQ_eq_twice_halfPair]
  constructor <;> intro h
  · linarith
  · rw [h]
    ring

/-- Every pure left/chiral direction is null for the neutral contact metric. -/
theorem left_half_null (x : ContactHalf) : neutralQ (x,(0,0)) = 0 := by
  rw [neutralQ_zero_iff_halfPair_zero]
  simp [halfPair]

/-- Every pure right/chiral direction is likewise null. -/
theorem right_half_null (y : ContactHalf) : neutralQ ((0,0),y) = 0 := by
  rw [neutralQ_zero_iff_halfPair_zero]
  simp [halfPair]

/-- The contact metric is genuinely split/indefinite: explicit positive and negative
vectors exist. -/
theorem neutral_signature_witnesses :
    neutralQ ((1,0),(1,0)) > 0 ∧ neutralQ ((1,0),(-1,0)) < 0 := by
  rw [neutralQ_eq_twice_halfPair, neutralQ_eq_twice_halfPair]
  norm_num [halfPair]

/-- Exchange of the two Lagrangian halves preserves the neutral quadratic form. -/
def exchangeHalves (u : ContactVector) : ContactVector := (u.2,u.1)

theorem neutralQ_exchangeHalves (u : ContactVector) :
    neutralQ (exchangeHalves u) = neutralQ u := by
  rw [neutralQ_eq_twice_halfPair, neutralQ_eq_twice_halfPair]
  rcases u with ⟨⟨x0,x1⟩,⟨y0,y1⟩⟩
  simp [exchangeHalves, halfPair]
  ring

/-- Consequently the second-order/contact-null condition is ambidextrous: it does not
prefer either Lagrangian half. -/
theorem contactNull_exchange_invariant (u : ContactVector) :
    neutralQ u = 0 ↔ neutralQ (exchangeHalves u) = 0 := by
  rw [neutralQ_exchangeHalves]

end GppAmbitwistorContactNeutralCone
