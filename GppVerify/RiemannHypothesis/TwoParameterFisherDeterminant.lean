import Mathlib.Tactic

/-!
# Two-parameter Fisher determinant algebra

For sufficient statistics `X` and `X^2`, the 2x2 covariance determinant is exactly
the determinant of the 3x3 moment Gram matrix of `(1,X,X^2)`.  For exactly
normalized finite supports with three or four points it is moreover a sum of
positive weight products times squared Vandermondes.  These are algebraic cores
of the two-parameter prime-gas fluctuation geometry; the infinite Gibbs-family
and measure-theoretic layers remain separate.
-/

namespace GppTwoParameterFisherDeterminant

/-- The covariance determinant of `(X,X^2)` equals the determinant of the moment
Gram matrix `E[(1,X,X^2)^T(1,X,X^2)]`, written in terms of moments `m₁,...,m₄`. -/
theorem covariance_det_eq_moment_gram_det
    (m1 m2 m3 m4 : ℝ) :
    (m2 - m1^2) * (m4 - m2^2) - (m3 - m1*m2)^2 =
      (m2*m4 - m3^2) - m1*(m1*m4 - m2*m3) + m2*(m1*m3 - m2^2) := by
  ring

/-- For a normalized three-point distribution, the covariance determinant of
`(X,X^2)` is exactly the weight product times the squared Vandermonde. -/
theorem three_point_covariance_det_eq_vandermonde
    (p q r x y z : ℝ) (hnorm : p + q + r = 1) :
    let m1 := p*x + q*y + r*z
    let m2 := p*x^2 + q*y^2 + r*z^2
    let m3 := p*x^3 + q*y^3 + r*z^3
    let m4 := p*x^4 + q*y^4 + r*z^4
    (m2 - m1^2) * (m4 - m2^2) - (m3 - m1*m2)^2 =
      p*q*r*(x-y)^2*(x-z)^2*(y-z)^2 := by
  dsimp
  have hr : r = 1 - p - q := by linarith
  rw [hr]
  ring

/-- The three-point Fisher determinant is strictly positive for positive weights
and pairwise distinct support points. -/
theorem three_point_covariance_det_pos
    (p q r x y z : ℝ)
    (hnorm : p + q + r = 1)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let m1 := p*x + q*y + r*z
    let m2 := p*x^2 + q*y^2 + r*z^2
    let m3 := p*x^3 + q*y^3 + r*z^3
    let m4 := p*x^4 + q*y^4 + r*z^4
    0 < (m2 - m1^2) * (m4 - m2^2) - (m3 - m1*m2)^2 := by
  dsimp
  rw [three_point_covariance_det_eq_vandermonde p q r x y z hnorm]
  have hxy2 : 0 < (x-y)^2 := by
    rw [pow_two]
    exact mul_self_pos.mpr (sub_ne_zero.mpr hxy)
  have hxz2 : 0 < (x-z)^2 := by
    rw [pow_two]
    exact mul_self_pos.mpr (sub_ne_zero.mpr hxz)
  have hyz2 : 0 < (y-z)^2 := by
    rw [pow_two]
    exact mul_self_pos.mpr (sub_ne_zero.mpr hyz)
  positivity

/-- Four-point Cauchy--Binet/Vandermonde identity.  The covariance determinant is
the sum over all three-point minors.  This is the first nontrivial finite-support
step beyond the minimal three-state certificate and exhibits the exact pattern
needed for the general finite Cauchy--Binet theorem. -/
theorem four_point_covariance_det_eq_vandermonde_sum
    (p q r s x y z w : ℝ) (hnorm : p + q + r + s = 1) :
    let m1 := p*x + q*y + r*z + s*w
    let m2 := p*x^2 + q*y^2 + r*z^2 + s*w^2
    let m3 := p*x^3 + q*y^3 + r*z^3 + s*w^3
    let m4 := p*x^4 + q*y^4 + r*z^4 + s*w^4
    (m2 - m1^2) * (m4 - m2^2) - (m3 - m1*m2)^2 =
      p*q*r*(x-y)^2*(x-z)^2*(y-z)^2 +
      p*q*s*(x-y)^2*(x-w)^2*(y-w)^2 +
      p*r*s*(x-z)^2*(x-w)^2*(z-w)^2 +
      q*r*s*(y-z)^2*(y-w)^2*(z-w)^2 := by
  dsimp
  have hs : s = 1 - p - q - r := by linarith
  rw [hs]
  ring

/-- For nonnegative normalized four-point weights, the two-parameter Fisher
covariance determinant is positive semidefinite for arbitrary support values. -/
theorem four_point_covariance_det_nonneg
    (p q r s x y z w : ℝ)
    (hnorm : p + q + r + s = 1)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    let m1 := p*x + q*y + r*z + s*w
    let m2 := p*x^2 + q*y^2 + r*z^2 + s*w^2
    let m3 := p*x^3 + q*y^3 + r*z^3 + s*w^3
    let m4 := p*x^4 + q*y^4 + r*z^4 + s*w^4
    0 ≤ (m2 - m1^2) * (m4 - m2^2) - (m3 - m1*m2)^2 := by
  dsimp
  rw [four_point_covariance_det_eq_vandermonde_sum p q r s x y z w hnorm]
  positivity

/-- A normalized four-point distribution has strictly positive Fisher determinant
as soon as one three-point subdistribution has positive weights and distinct
support, while the remaining weight is merely nonnegative.  No distinctness
assumption on the fourth support point is required. -/
theorem four_point_covariance_det_pos_of_three
    (p q r s x y z w : ℝ)
    (hnorm : p + q + r + s = 1)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 ≤ s)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let m1 := p*x + q*y + r*z + s*w
    let m2 := p*x^2 + q*y^2 + r*z^2 + s*w^2
    let m3 := p*x^3 + q*y^3 + r*z^3 + s*w^3
    let m4 := p*x^4 + q*y^4 + r*z^4 + s*w^4
    0 < (m2 - m1^2) * (m4 - m2^2) - (m3 - m1*m2)^2 := by
  dsimp
  rw [four_point_covariance_det_eq_vandermonde_sum p q r s x y z w hnorm]
  have hxy2 : 0 < (x-y)^2 := by
    rw [pow_two]
    exact mul_self_pos.mpr (sub_ne_zero.mpr hxy)
  have hxz2 : 0 < (x-z)^2 := by
    rw [pow_two]
    exact mul_self_pos.mpr (sub_ne_zero.mpr hxz)
  have hyz2 : 0 < (y-z)^2 := by
    rw [pow_two]
    exact mul_self_pos.mpr (sub_ne_zero.mpr hyz)
  have hfirst : 0 < p*q*r*(x-y)^2*(x-z)^2*(y-z)^2 := by positivity
  have hsecond : 0 ≤ p*q*s*(x-y)^2*(x-w)^2*(y-w)^2 := by positivity
  have hthird : 0 ≤ p*r*s*(x-z)^2*(x-w)^2*(z-w)^2 := by positivity
  have hfourth : 0 ≤ q*r*s*(y-z)^2*(y-w)^2*(z-w)^2 := by positivity
  linarith

end GppTwoParameterFisherDeterminant

#print axioms GppTwoParameterFisherDeterminant.covariance_det_eq_moment_gram_det
#print axioms GppTwoParameterFisherDeterminant.three_point_covariance_det_eq_vandermonde
#print axioms GppTwoParameterFisherDeterminant.three_point_covariance_det_pos
#print axioms GppTwoParameterFisherDeterminant.four_point_covariance_det_eq_vandermonde_sum
#print axioms GppTwoParameterFisherDeterminant.four_point_covariance_det_nonneg
#print axioms GppTwoParameterFisherDeterminant.four_point_covariance_det_pos_of_three
