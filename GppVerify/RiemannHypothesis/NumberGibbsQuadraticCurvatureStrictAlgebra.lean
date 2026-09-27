import GppVerify.RiemannHypothesis.NumberGibbsQuadraticCurvatureAlgebra
import Mathlib.Tactic

/-!
# Strict quadratic number-gas curvature algebra

This module isolates the strict form of the already-certified curvature reduction.
It does not assume any additional arithmetic input: once the cubic residual square
moment is strictly positive and the centered metric determinant is positive, the
centered degree-three Gram determinant is strictly positive and scalar curvature
is strictly below one half.
-/

namespace GppNumberGibbsQuadraticCurvatureStrictAlgebra

open GppNumberGibbsQuadraticCurvatureAlgebra

/-- Strict positivity of the residual square moment and of the metric determinant
forces strict positivity of the centered degree-three Gram determinant. -/
theorem centeredGramDet_pos_of_residualSqMoment_pos
    (m2 m3 m4 m5 m6 : ℝ)
    (hD : 0 < metricDet m2 m3 m4)
    (hres : 0 < residualSqMoment m2 m3 m4 m5 m6) :
    0 < centeredGramDet m2 m3 m4 m5 m6 := by
  rw [residualSqMoment_eq_metric_mul_centeredGramDet] at hres
  by_contra hH
  have hHnonpos : centeredGramDet m2 m3 m4 m5 m6 ≤ 0 := le_of_not_gt hH
  have hprod :
      metricDet m2 m3 m4 * centeredGramDet m2 m3 m4 m5 m6 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hD.le hHnonpos
  linarith

/-- Strict centered-Gram positivity gives the strict scalar-curvature ceiling. -/
theorem scalarCurvature_lt_half
    (m2 m3 m4 m5 m6 : ℝ)
    (hD : metricDet m2 m3 m4 ≠ 0)
    (hH : 0 < centeredGramDet m2 m3 m4 m5 m6) :
    scalarCurvature m2 m3 m4 m5 m6 < (1 : ℝ) / 2 := by
  rw [scalarCurvature_eq_half_sub m2 m3 m4 m5 m6 hD]
  have hDsq : 0 < metricDet m2 m3 m4 ^ 2 := sq_pos_of_ne_zero hD
  have hratio :
      0 < centeredGramDet m2 m3 m4 m5 m6 / metricDet m2 m3 m4 ^ 2 :=
    div_pos hH hDsq
  linarith

/-- Strict residual-square positivity is the exact semantic condition needed for
`R < 1/2` once the centered metric is nondegenerate. -/
theorem scalarCurvature_lt_half_of_residualSqMoment_pos
    (m2 m3 m4 m5 m6 : ℝ)
    (hD : 0 < metricDet m2 m3 m4)
    (hres : 0 < residualSqMoment m2 m3 m4 m5 m6) :
    scalarCurvature m2 m3 m4 m5 m6 < (1 : ℝ) / 2 := by
  exact scalarCurvature_lt_half m2 m3 m4 m5 m6 hD.ne'
    (centeredGramDet_pos_of_residualSqMoment_pos m2 m3 m4 m5 m6 hD hres)

end GppNumberGibbsQuadraticCurvatureStrictAlgebra

#print axioms GppNumberGibbsQuadraticCurvatureStrictAlgebra.centeredGramDet_pos_of_residualSqMoment_pos
#print axioms GppNumberGibbsQuadraticCurvatureStrictAlgebra.scalarCurvature_lt_half
#print axioms GppNumberGibbsQuadraticCurvatureStrictAlgebra.scalarCurvature_lt_half_of_residualSqMoment_pos
