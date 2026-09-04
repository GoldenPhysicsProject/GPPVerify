import Mathlib.Tactic
import GppVerify.CelestialHolography.TwistorCanonicalShift

/-!
# Canonical duality of the two graviton twistor weights

A key structural fact in twistor gravity is that the two helicity sectors do not
live in unrelated line-bundle degrees.  On projective twistor space `PT ≃ CP^3`,
whose canonical bundle has degree `-4`, the canonical/Serre dual of a line bundle
of degree `k` has degree

  -k - 4.

For the gravitational deformation field `h` of degree `+2`, this gives degree `-6`,
which is exactly the degree of the opposite-helicity field usually denoted `g`, `B`,
or `\tilde h` in twistor actions.

This file formalizes the degree-level statement only.  It does NOT claim that a
section of `O(-6)` is determined canonically by a section of `O(2)`.  A bundle-level
duality fixes the target representation, not a preferred element of its section
space.  Constructing such an element requires additional structure (pairing, real
structure, field equation, polarization, etc.).
-/

namespace GppTwistorDiagonalDuality

open GppTwistorCanonicalShift

/-- Pure representation dualization reverses the degree. -/
def chargeDualWeight (k : ℤ) : ℤ := -k

/-- The canonical orientation/top-form shift on `CP^3` contributes degree `-4`. -/
def canonicalShiftedDualWeight (k : ℤ) : ℤ := chargeDualWeight k + canonicalDegree

/-- The combined dualization plus canonical shift is exactly the Serre/Fourier reflection. -/
theorem canonicalShiftedDualWeight_eq_serreWeight (k : ℤ) :
    canonicalShiftedDualWeight k = serreWeight k := by
  norm_num [canonicalShiftedDualWeight, chargeDualWeight, serreWeight,
    canonicalDegree, projectiveTwistorDim]

/-- The diagonal duality is involutive at the level of line-bundle degree. -/
theorem canonicalShiftedDualWeight_involutive (k : ℤ) :
    canonicalShiftedDualWeight (canonicalShiftedDualWeight k) = k := by
  rw [canonicalShiftedDualWeight_eq_serreWeight,
      canonicalShiftedDualWeight_eq_serreWeight]
  exact serreWeight_involutive k

/-- Gravity: the deformation weight `O(2)` is sent exactly to `O(-6)`. -/
theorem graviton_deformation_to_conjugate :
    canonicalShiftedDualWeight 2 = -6 := by
  norm_num [canonicalShiftedDualWeight, chargeDualWeight, canonicalDegree,
    projectiveTwistorDim]

/-- And the opposite-helicity weight returns to the deformation weight. -/
theorem graviton_conjugate_to_deformation :
    canonicalShiftedDualWeight (-6) = 2 := by
  norm_num [canonicalShiftedDualWeight, chargeDualWeight, canonicalDegree,
    projectiveTwistorDim]

/-- Yang--Mills analogue: `O(0)` and `O(-4)` form the same canonical-dual pair. -/
theorem gauge_field_pair :
    canonicalShiftedDualWeight 0 = -4 ∧
    canonicalShiftedDualWeight (-4) = 0 := by
  norm_num [canonicalShiftedDualWeight, chargeDualWeight, canonicalDegree,
    projectiveTwistorDim]

/-- In doubled-helicity variables this same operation reverses helicity. -/
theorem diagonal_duality_flips_helicity (n : ℤ) :
    canonicalShiftedDualWeight (GppTwistorWeightDuality.twistorWeight n)
      = GppTwistorWeightDuality.twistorWeight (-n) := by
  rw [canonicalShiftedDualWeight_eq_serreWeight]
  exact serreWeight_is_helicityFlip n

end GppTwistorDiagonalDuality
