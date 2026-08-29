import Mathlib.Tactic

/-!
# Finite Fisher moment bridge

This module isolates the scalar algebra sitting between the finite-support
Vandermonde energy and the two-parameter Fisher determinant for sufficient
statistics `X` and `X^2`.

The normalized covariance determinant is only one slice of a more useful
homogeneous identity.  For raw finite truncations whose total mass `m₀` need
not yet equal one, `fisherNumerator` is the division-free covariance
numerator.  This is the correct object for passing unnormalized finite
truncations to a normalized countable limit.
-/

namespace GppFiniteFisherMomentBridge

/-- Determinant of the covariance matrix of `X` and `X^2`, written in terms of
raw moments `m₁,...,m₄` for normalized mass. -/
def fisherDet (m1 m2 m3 m4 : ℝ) : ℝ :=
  (m2 - m1 ^ 2) * (m4 - m2 ^ 2) - (m3 - m1 * m2) ^ 2

/-- Division-free covariance determinant numerator for arbitrary total mass
`m₀`.  If `m₀ = 1`, this reduces exactly to `fisherDet`. -/
def fisherNumerator (m0 m1 m2 m3 m4 : ℝ) : ℝ :=
  (m0 * m2 - m1 ^ 2) * (m0 * m4 - m2 ^ 2) -
    (m0 * m3 - m1 * m2) ^ 2

/-- The cubic moment discriminant produced by expanding an ordered squared
Vandermonde energy.  The `m0` argument is the total mass. -/
def momentDiscriminant (m0 m1 m2 m3 m4 : ℝ) : ℝ :=
  6 * (m0 * m2 * m4 + 2 * m1 * m2 * m3 - m2 ^ 3 - m0 * m3 ^ 2 - m1 ^ 2 * m4)

/-- General-mass bridge: six times the division-free Fisher covariance
numerator equals total mass times the Vandermonde moment discriminant.

This identity avoids falsely normalizing finite truncations of a countable
probability distribution. -/
theorem six_fisherNumerator_eq_mass_mul_momentDiscriminant
    (m0 m1 m2 m3 m4 : ℝ) :
    6 * fisherNumerator m0 m1 m2 m3 m4 =
      m0 * momentDiscriminant m0 m1 m2 m3 m4 := by
  unfold fisherNumerator momentDiscriminant
  ring

/-- At unit total mass, the general numerator is the ordinary Fisher
determinant. -/
theorem fisherNumerator_one_eq_fisherDet
    (m1 m2 m3 m4 : ℝ) :
    fisherNumerator 1 m1 m2 m3 m4 = fisherDet m1 m2 m3 m4 := by
  unfold fisherNumerator fisherDet
  ring

/-- At normalized total mass `m₀ = 1`, the moment discriminant is exactly six
times the Fisher covariance determinant. -/
theorem momentDiscriminant_one_eq_six_fisherDet
    (m1 m2 m3 m4 : ℝ) :
    momentDiscriminant 1 m1 m2 m3 m4 = 6 * fisherDet m1 m2 m3 m4 := by
  unfold momentDiscriminant fisherDet
  ring

/-- Equivalent division-free form useful for composing with an ordered-energy
identity. -/
theorem six_fisherDet_eq_momentDiscriminant_one
    (m1 m2 m3 m4 : ℝ) :
    6 * fisherDet m1 m2 m3 m4 = momentDiscriminant 1 m1 m2 m3 m4 := by
  symm
  exact momentDiscriminant_one_eq_six_fisherDet m1 m2 m3 m4

end GppFiniteFisherMomentBridge

#print axioms GppFiniteFisherMomentBridge.six_fisherNumerator_eq_mass_mul_momentDiscriminant
#print axioms GppFiniteFisherMomentBridge.fisherNumerator_one_eq_fisherDet
#print axioms GppFiniteFisherMomentBridge.momentDiscriminant_one_eq_six_fisherDet
#print axioms GppFiniteFisherMomentBridge.six_fisherDet_eq_momentDiscriminant_one
