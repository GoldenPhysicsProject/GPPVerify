import Mathlib.Tactic
import GppVerify.CelestialHolography.LorentzNullConeOrientation

/-!
# Celestial projectivization forgets the future/past orientation of a null ray

A celestial point is a projective null DIRECTION.  Projectivization identifies nonzero
scalar multiples, in particular

  p ~ -p.

But on the Lorentzian real null cone the two representatives have opposite time orientation:
`p` and `-p` lie on the future and past components respectively (away from the zero vector).
Therefore an unoriented projective celestial direction forgets precisely the discrete sign
`t=+/-1` introduced in `LorentzNullConeOrientation`.

This gives a geometric home for the project's hidden time/worldline sign that is independent
of charge and independent of the left/right chirality exchange: the celestial sphere is the
base of an ORIENTED-null-ray double cover.  Globally, future and past null infinity provide
natural places for the two oriented copies, although identifying the finite sign here with a
specific global I+/I- scattering map requires the asymptotic spacetime construction.

An important consequence for the broader project is that celestial shadow/Mellin inversion
should not automatically be called time reversal.  Shadow acts on representation data on a
projective celestial direction; the future/past ray orientation is an additional discrete
piece that projectivization has already discarded.
-/

namespace GppCelestialOrientedNullDoubleCover

open GppLorentzHermitianDiscreteGeometry
open GppLorentzNullConeOrientation

/-- Finite projective equivalence on nonzero real four-vectors. -/
def ProjectivelyEquivalent (v w : R4) : Prop :=
  ∃ a : ℝ, a ≠ 0 ∧ w =
    (a*v.1,a*v.2.1,a*v.2.2.1,a*v.2.2.2)

/-- Negating a nonzero vector does not change its projective direction. -/
theorem neg_projectively_equivalent (v : R4) :
    ProjectivelyEquivalent v (-v.1,-v.2.1,-v.2.2.1,-v.2.2.2) := by
  refine ⟨-1, by norm_num, ?_⟩
  simp

/-- The two canonical oriented null lifts of one spinor square define the same projective
celestial direction. -/
theorem future_past_same_projective_direction (s : RealSpinor4) :
    ProjectivelyEquivalent (orientedNullVector 1 s) (orientedNullVector (-1) s) := by
  rw [orientedNullVector_flip]
  exact neg_projectively_equivalent (orientedNullVector 1 s)

/-- Yet their time components are opposite. -/
theorem future_past_opposite_time_component (s : RealSpinor4) :
    (orientedNullVector (-1) s).1 = -(orientedNullVector 1 s).1 := by
  simp [orientedNullVector]

/-- Both oriented lifts remain null. -/
theorem oriented_pair_both_null (s : RealSpinor4) :
    minkowskiQ (orientedNullVector 1 s) = 0 ∧
    minkowskiQ (orientedNullVector (-1) s) = 0 := by
  exact ⟨orientedNullVector_is_null 1 s, orientedNullVector_is_null (-1) s⟩

/-- Finite capstone: same projective direction, opposite orientation, same null condition. -/
theorem celestial_forgets_orientation_capstone (s : RealSpinor4) :
    ProjectivelyEquivalent (orientedNullVector 1 s) (orientedNullVector (-1) s) ∧
    (orientedNullVector (-1) s).1 = -(orientedNullVector 1 s).1 ∧
    minkowskiQ (orientedNullVector 1 s) = 0 ∧
    minkowskiQ (orientedNullVector (-1) s) = 0 := by
  exact ⟨future_past_same_projective_direction s,
    future_past_opposite_time_component s,
    (oriented_pair_both_null s).1,
    (oriented_pair_both_null s).2⟩

end GppCelestialOrientedNullDoubleCover
