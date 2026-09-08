import Mathlib.Tactic
import GppVerify.CelestialHolography.CelestialOrientedNullDoubleCover
import GppVerify.StandardModel.GaugeGravityDiagonalBlindness

/-!
# Crossing as simultaneous gauge conjugation and oriented-momentum reversal

Relativistic scattering normally uses an all-outgoing analytic convention.  At the finite
kinematic level, crossing an incoming charged leg to the outgoing side reverses its
four-momentum representative and replaces the particle representation by the conjugate one:

  (q,p) -> (-q,-p)

for an Abelian charge label.  Spin/helicity wavefunctions and analytic continuation carry
additional structure not modeled here.

This finite core is EXACTLY the diagonal quotient studied in the project's orientation
programme:

  q p is invariant,
  p^2/mass shell is invariant,
  the projective celestial direction is unchanged because p~-p,
  but the oriented future/past/in-out lift is reversed.

Thus the relation `(q,t)~(-q,-t)` is not merely a cosmological thought experiment; it is the
same sign algebra already built into crossing between incoming particles and outgoing
antiparticles.  What is new to investigate is whether this crossing/orientation quotient is
also the correct global geometric language for CPT-paired matter and the I-/I+ celestial
state spaces.
-/

namespace GppCelestialCrossingChargeOrientation

open GppLorentzHermitianDiscreteGeometry
open GppCelestialOrientedNullDoubleCover
open GppGaugeGravityDiagonalBlindness

/-- Minimal oriented charged leg. -/
structure OrientedChargedLeg where
  q : ℝ
  p : R4
  deriving DecidableEq

/-- Finite sign core of crossing to the opposite in/out orientation. -/
def crossLeg (L : OrientedChargedLeg) : OrientedChargedLeg :=
  ⟨-L.q, scaleR4 (-1) L.p⟩

/-- Crossing twice restores the finite labels. -/
theorem crossLeg_involution (L : OrientedChargedLeg) : crossLeg (crossLeg L) = L := by
  cases L with
  | mk q p =>
    rcases p with ⟨t,x,y,z⟩
    simp [crossLeg, scaleR4]

/-- The gauge/worldline current is exactly invariant under the crossing sign core. -/
theorem crossing_current_invariant (L : OrientedChargedLeg) :
    current4 (crossLeg L).q (crossLeg L).p = current4 L.q L.p := by
  cases L
  exact current_diagonal_flip_invariant _ _

/-- The Minkowski mass-shell quadratic form is unchanged by momentum reversal. -/
theorem crossing_massShell_invariant (L : OrientedChargedLeg) :
    minkowskiQ (crossLeg L).p = minkowskiQ L.p := by
  rcases L with ⟨q,⟨t,x,y,z⟩⟩
  simp [crossLeg, scaleR4, minkowskiQ]
  ring

/-- The two momentum representatives have the same projective celestial direction. -/
theorem crossing_same_projective_direction (L : OrientedChargedLeg) :
    ProjectivelyEquivalent L.p (crossLeg L).p := by
  rcases L with ⟨q,⟨t,x,y,z⟩⟩
  refine ⟨-1, by norm_num, ?_⟩
  simp [crossLeg, scaleR4]

/-- Crossing flips charge and oriented momentum while preserving their relational product. -/
theorem crossing_diagonal_package (L : OrientedChargedLeg) :
    (crossLeg L).q = -L.q ∧
    (crossLeg L).p = scaleR4 (-1) L.p ∧
    current4 (crossLeg L).q (crossLeg L).p = current4 L.q L.p ∧
    minkowskiQ (crossLeg L).p = minkowskiQ L.p := by
  exact ⟨rfl,rfl,crossing_current_invariant L,crossing_massShell_invariant L⟩

end GppCelestialCrossingChargeOrientation
