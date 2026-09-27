import GppVerify.RiemannHypothesis.NumberGibbsQuadraticMassieuMetric
import Mathlib.Tactic

/-!
# Algebraic curvature reduction for the quadratic number-Gibbs metric

This file isolates the exact centered-moment algebra discovered for the
quadratically confined two-parameter Gibbs family.  It deliberately proves only
the polynomial/rational identities and the resulting conditional curvature
bound.  The analytic identification of these symbols with countable Gibbs
centered moments, and the nonnegativity of the degree-three moment Gram
determinant, remain separate semantic obligations.
-/

namespace GppNumberGibbsQuadraticCurvatureAlgebra

/-- Determinant of the covariance metric of the sufficient statistics `X` and
`X^2`, expressed in centered moments. -/
def metricDet (m2 m3 m4 : ℝ) : ℝ :=
  m2 * m4 - m3 ^ 2 - m2 ^ 3

/-- Determinant of the centered degree-three moment Gram matrix, expanded as a
polynomial in centered moments `m₂,...,m₆`. -/
def centeredGramDet (m2 m3 m4 m5 m6 : ℝ) : ℝ :=
  -m2 ^ 3 * m6 + 2 * m2 ^ 2 * m3 * m5 + m2 ^ 2 * m4 ^ 2
    - 3 * m2 * m3 ^ 2 * m4 + m2 * m4 * m6 - m2 * m5 ^ 2
    + m3 ^ 4 - m3 ^ 2 * m6 + 2 * m3 * m4 * m5 - m4 ^ 3

/-- Determinant of the `3×3` Hessian-curvature numerator matrix after exact
elimination of the mean. -/
def curvatureNumeratorDet (m2 m3 m4 m5 m6 : ℝ) : ℝ :=
  -m2 ^ 6 + 2 * m2 ^ 4 * m4 - 2 * m2 ^ 3 * m3 ^ 2 - m2 ^ 3 * m6
    + 2 * m2 ^ 2 * m3 * m5 - m2 * m3 ^ 2 * m4 + m2 * m4 * m6
    - m2 * m5 ^ 2 - m3 ^ 2 * m6 + 2 * m3 * m4 * m5 - m4 ^ 3

/-- Exact polynomial elimination identity:
`det(C) = det(H) - det(g)^2`. -/
theorem curvatureNumeratorDet_eq_gram_sub_metric_sq
    (m2 m3 m4 m5 m6 : ℝ) :
    curvatureNumeratorDet m2 m3 m4 m5 m6 =
      centeredGramDet m2 m3 m4 m5 m6 - metricDet m2 m3 m4 ^ 2 := by
  unfold curvatureNumeratorDet centeredGramDet metricDet
  ring

/-- Constant coefficient of the denominator-cleared monic cubic residual
orthogonal to `1,Y,Y²` when the centered moments are `m₂,...,m₅`. -/
def residualC0 (m2 m3 m4 m5 : ℝ) : ℝ :=
  m2 ^ 2 * m5 - 2 * m2 * m3 * m4 + m3 ^ 3

/-- Linear coefficient of the denominator-cleared cubic residual. -/
def residualC1 (m2 m3 m4 m5 : ℝ) : ℝ :=
  m2 ^ 2 * m4 - m2 * m3 ^ 2 + m3 * m5 - m4 ^ 2

/-- Quadratic coefficient of the denominator-cleared cubic residual. -/
def residualC2 (m2 m3 m4 m5 : ℝ) : ℝ :=
  m2 ^ 2 * m3 - m2 * m5 + m3 * m4

/-- The centered expectation of the square of
`D Y³ + C₂ Y² + C₁ Y + C₀`, written purely in moments.  The missing first
moment term vanishes because `Y` is centered. -/
def residualSqMoment (m2 m3 m4 m5 m6 : ℝ) : ℝ :=
  let D := metricDet m2 m3 m4
  let A := residualC0 m2 m3 m4 m5
  let B := residualC1 m2 m3 m4 m5
  let C := residualC2 m2 m3 m4 m5
  A ^ 2 + B ^ 2 * m2 + C ^ 2 * m4 + D ^ 2 * m6
    + 2 * A * C * m2 + 2 * A * D * m3 + 2 * B * C * m3
    + 2 * B * D * m4 + 2 * C * D * m5

/-- Exact Schur-complement/Cramer's-rule identity for the centered moment Gram
matrix.  The squared cubic residual equals `det(g) * det(H)`.  This is the
useful semantic interface for the countable Gibbs model: its left-hand side can
be realized directly as an expectation of a pointwise square. -/
theorem residualSqMoment_eq_metric_mul_centeredGramDet
    (m2 m3 m4 m5 m6 : ℝ) :
    residualSqMoment m2 m3 m4 m5 m6 =
      metricDet m2 m3 m4 * centeredGramDet m2 m3 m4 m5 m6 := by
  unfold residualSqMoment residualC0 residualC1 residualC2 metricDet centeredGramDet
  ring

/-- Once the metric determinant is strictly positive, nonnegativity of the
single cubic residual square moment implies nonnegativity of the full centered
`4×4` Gram determinant. -/
theorem centeredGramDet_nonneg_of_residualSqMoment_nonneg
    (m2 m3 m4 m5 m6 : ℝ)
    (hD : 0 < metricDet m2 m3 m4)
    (hres : 0 ≤ residualSqMoment m2 m3 m4 m5 m6) :
    0 ≤ centeredGramDet m2 m3 m4 m5 m6 := by
  rw [residualSqMoment_eq_metric_mul_centeredGramDet] at hres
  by_contra hH
  have hHneg : centeredGramDet m2 m3 m4 m5 m6 < 0 := lt_of_not_ge hH
  have hprod :
      metricDet m2 m3 m4 * centeredGramDet m2 m3 m4 m5 m6 < 0 :=
    mul_neg_of_pos_of_neg hD hHneg
  linarith

/-- Scalar-curvature normal form used by the quadratic number-gas discovery
calculation. -/
noncomputable def scalarCurvature
    (m2 m3 m4 m5 m6 : ℝ) : ℝ :=
  (metricDet m2 m3 m4 ^ 2 - centeredGramDet m2 m3 m4 m5 m6) /
    (2 * metricDet m2 m3 m4 ^ 2)

/-- When the metric determinant is nonzero, the curvature is exactly one half
minus one half of the normalized centered Gram determinant. -/
theorem scalarCurvature_eq_half_sub
    (m2 m3 m4 m5 m6 : ℝ)
    (hD : metricDet m2 m3 m4 ≠ 0) :
    scalarCurvature m2 m3 m4 m5 m6 =
      (1 : ℝ) / 2 *
        (1 - centeredGramDet m2 m3 m4 m5 m6 / metricDet m2 m3 m4 ^ 2) := by
  unfold scalarCurvature
  field_simp [hD]

/-- Algebraic curvature ceiling.  Once the centered degree-three moment Gram
determinant is known nonnegative, strict metric nondegeneracy implies `R ≤ 1/2`.
No sign-definiteness of `R` itself is asserted. -/
theorem scalarCurvature_le_half
    (m2 m3 m4 m5 m6 : ℝ)
    (hD : metricDet m2 m3 m4 ≠ 0)
    (hH : 0 ≤ centeredGramDet m2 m3 m4 m5 m6) :
    scalarCurvature m2 m3 m4 m5 m6 ≤ (1 : ℝ) / 2 := by
  rw [scalarCurvature_eq_half_sub m2 m3 m4 m5 m6 hD]
  have hDsq : 0 < metricDet m2 m3 m4 ^ 2 := sq_pos_of_ne_zero hD
  have hratio :
      0 ≤ centeredGramDet m2 m3 m4 m5 m6 / metricDet m2 m3 m4 ^ 2 :=
    div_nonneg hH hDsq.le
  linarith

/-- Curvature ceiling in the form needed by the countable Gibbs bridge: strict
metric positivity plus nonnegativity of one explicit cubic residual square
moment suffice. -/
theorem scalarCurvature_le_half_of_residualSqMoment_nonneg
    (m2 m3 m4 m5 m6 : ℝ)
    (hD : 0 < metricDet m2 m3 m4)
    (hres : 0 ≤ residualSqMoment m2 m3 m4 m5 m6) :
    scalarCurvature m2 m3 m4 m5 m6 ≤ (1 : ℝ) / 2 := by
  exact scalarCurvature_le_half m2 m3 m4 m5 m6 hD.ne'
    (centeredGramDet_nonneg_of_residualSqMoment_nonneg m2 m3 m4 m5 m6 hD hres)

end GppNumberGibbsQuadraticCurvatureAlgebra

#print axioms GppNumberGibbsQuadraticCurvatureAlgebra.curvatureNumeratorDet_eq_gram_sub_metric_sq
#print axioms GppNumberGibbsQuadraticCurvatureAlgebra.residualSqMoment_eq_metric_mul_centeredGramDet
#print axioms GppNumberGibbsQuadraticCurvatureAlgebra.centeredGramDet_nonneg_of_residualSqMoment_nonneg
#print axioms GppNumberGibbsQuadraticCurvatureAlgebra.scalarCurvature_eq_half_sub
#print axioms GppNumberGibbsQuadraticCurvatureAlgebra.scalarCurvature_le_half
#print axioms GppNumberGibbsQuadraticCurvatureAlgebra.scalarCurvature_le_half_of_residualSqMoment_nonneg
