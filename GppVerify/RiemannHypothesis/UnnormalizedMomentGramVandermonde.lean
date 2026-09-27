import Mathlib.Tactic

/-!
# Unnormalized moment-Gram Vandermonde identities

For a positive discrete measure, the 3x3 moment Gram determinant for the
observables `(1, X, X^2)` is a Cauchy--Binet sum of squared Vandermonde minors.
Unlike the covariance formulas, these identities require no normalization of
finite prefixes.  This is the finite algebraic interface needed to pass from
finite truncations to a countable Gibbs measure by convergence of moments
`m₀,...,m₄`.
-/

namespace GppUnnormalizedMomentGramVandermonde

/-- Exact three-state moment-Gram determinant, with no normalization assumption. -/
theorem three_point_moment_gram_det_eq_vandermonde
    (p q r x y z : ℝ) :
    let m0 := p + q + r
    let m1 := p*x + q*y + r*z
    let m2 := p*x^2 + q*y^2 + r*z^2
    let m3 := p*x^3 + q*y^3 + r*z^3
    let m4 := p*x^4 + q*y^4 + r*z^4
    m0 * (m2*m4 - m3^2) - m1 * (m1*m4 - m2*m3) +
      m2 * (m1*m3 - m2^2) =
      p*q*r*(x-y)^2*(x-z)^2*(y-z)^2 := by
  dsimp
  ring

/-- Exact four-state Cauchy--Binet identity for the unnormalized moment Gram
matrix.  Every term is a weight triple times a squared Vandermonde. -/
theorem four_point_moment_gram_det_eq_vandermonde_sum
    (p q r s x y z w : ℝ) :
    let m0 := p + q + r + s
    let m1 := p*x + q*y + r*z + s*w
    let m2 := p*x^2 + q*y^2 + r*z^2 + s*w^2
    let m3 := p*x^3 + q*y^3 + r*z^3 + s*w^3
    let m4 := p*x^4 + q*y^4 + r*z^4 + s*w^4
    m0 * (m2*m4 - m3^2) - m1 * (m1*m4 - m2*m3) +
      m2 * (m1*m3 - m2^2) =
      p*q*r*(x-y)^2*(x-z)^2*(y-z)^2 +
      p*q*s*(x-y)^2*(x-w)^2*(y-w)^2 +
      p*r*s*(x-z)^2*(x-w)^2*(z-w)^2 +
      q*r*s*(y-z)^2*(y-w)^2*(z-w)^2 := by
  dsimp
  ring

/-- For nonnegative four-state weights, the unnormalized moment Gram
determinant dominates any selected three-state Vandermonde witness. -/
theorem four_point_moment_gram_det_ge_first_vandermonde
    (p q r s x y z w : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    let m0 := p + q + r + s
    let m1 := p*x + q*y + r*z + s*w
    let m2 := p*x^2 + q*y^2 + r*z^2 + s*w^2
    let m3 := p*x^3 + q*y^3 + r*z^3 + s*w^3
    let m4 := p*x^4 + q*y^4 + r*z^4 + s*w^4
    p*q*r*(x-y)^2*(x-z)^2*(y-z)^2 ≤
      m0 * (m2*m4 - m3^2) - m1 * (m1*m4 - m2*m3) +
        m2 * (m1*m3 - m2^2) := by
  dsimp
  rw [four_point_moment_gram_det_eq_vandermonde_sum p q r s x y z w]
  have hsecond : 0 ≤ p*q*s*(x-y)^2*(x-w)^2*(y-w)^2 := by positivity
  have hthird : 0 ≤ p*r*s*(x-z)^2*(x-w)^2*(z-w)^2 := by positivity
  have hfourth : 0 ≤ q*r*s*(y-z)^2*(y-w)^2*(z-w)^2 := by positivity
  linarith

end GppUnnormalizedMomentGramVandermonde

#print axioms GppUnnormalizedMomentGramVandermonde.three_point_moment_gram_det_eq_vandermonde
#print axioms GppUnnormalizedMomentGramVandermonde.four_point_moment_gram_det_eq_vandermonde_sum
#print axioms GppUnnormalizedMomentGramVandermonde.four_point_moment_gram_det_ge_first_vandermonde
