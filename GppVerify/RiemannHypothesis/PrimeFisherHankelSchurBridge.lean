import Mathlib.Tactic

/-!
# Prime-gas Fisher covariance as a Hankel Schur complement

The all-order prime-gas polynomial Gram program naturally produces the raw moment
Hankel matrix

  [m0 m1 m2]
  [m1 m2 m3]
  [m2 m3 m4].

The two-parameter Fisher covariance matrix for the observables `x` and `x^2` is
the Schur complement of the scalar mass `m0`.  This file records the exact algebraic
identity

  det(H3) = m0^3 det(Cov(x,x^2)).

Thus strict positivity of the three-by-three raw Hankel determinant, together with
positive total mass, transfers immediately to strict two-parameter Fisher geometry.
No probabilistic or zeta-specific assumption is hidden in this algebraic bridge.
-/

namespace GppPrimeFisherHankelSchurBridge

/-- Determinant of the normalized covariance matrix of the observables `x` and `x^2`
written solely in terms of raw moments `m0,...,m4`. -/
noncomputable def centeredCovDet
    (m0 m1 m2 m3 m4 : ℝ) : ℝ :=
  (m2 / m0 - (m1 / m0) ^ 2) *
      (m4 / m0 - (m2 / m0) ^ 2) -
    (m3 / m0 - (m1 / m0) * (m2 / m0)) ^ 2

/-- Explicit determinant of the symmetric three-by-three Hankel moment matrix. -/
def hankel3Det (m0 m1 m2 m3 m4 : ℝ) : ℝ :=
  m0 * (m2 * m4 - m3 ^ 2) -
    m1 * (m1 * m4 - m2 * m3) +
    m2 * (m1 * m3 - m2 ^ 2)

/-- **Schur-complement identity.**  For nonzero total mass `m0`, the raw Hankel
determinant is exactly `m0^3` times the centered two-observable covariance
determinant. -/
theorem hankel3Det_eq_mass_cube_mul_centeredCovDet
    {m0 m1 m2 m3 m4 : ℝ} (hm0 : m0 ≠ 0) :
    hankel3Det m0 m1 m2 m3 m4 =
      m0 ^ 3 * centeredCovDet m0 m1 m2 m3 m4 := by
  unfold hankel3Det centeredCovDet
  field_simp [hm0]
  ring

/-- Strict raw Hankel positivity transfers to strict two-parameter Fisher covariance
positivity when the total mass is positive. -/
theorem centeredCovDet_pos_of_hankel3Det_pos
    {m0 m1 m2 m3 m4 : ℝ}
    (hm0 : 0 < m0)
    (hdet : 0 < hankel3Det m0 m1 m2 m3 m4) :
    0 < centeredCovDet m0 m1 m2 m3 m4 := by
  have hm0ne : m0 ≠ 0 := hm0.ne'
  have hmass : 0 < m0 ^ 3 := pow_pos hm0 3
  rw [hankel3Det_eq_mass_cube_mul_centeredCovDet hm0ne] at hdet
  rcases (mul_pos_iff.mp hdet) with h | h
  · exact h.2
  · exact False.elim ((not_lt_of_ge hmass.le) h.1)

end GppPrimeFisherHankelSchurBridge

#print axioms GppPrimeFisherHankelSchurBridge.hankel3Det_eq_mass_cube_mul_centeredCovDet
#print axioms GppPrimeFisherHankelSchurBridge.centeredCovDet_pos_of_hankel3Det_pos
