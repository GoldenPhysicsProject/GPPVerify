import GppVerify.RiemannHypothesis.NumberGibbsQuadraticCurvatureAlgebra
import GppVerify.RiemannHypothesis.NumberGibbsQuadraticCurvatureSummability
import GppVerify.RiemannHypothesis.NumberGibbsQuadraticThermodynamics
import Mathlib.Tactic

/-!
# Countable Gibbs square-positivity bridge for quadratic curvature

This file supplies the analytic positivity half of the curvature bridge.  For the
actual quadratically confined countable Gibbs measure, every normalized weighted
square is nonnegative.  In particular this applies to the denominator-cleared
cubic residual whose symbolic square moment is already proved to equal
`metricDet * centeredGramDet`.

The exact pointwise sixth-order expansion of that cubic square is also formalized
here.  Consequently the remaining semantic obligation is purely the `tsum`
identification of normalized centered powers with the actual centered moments
through order six; no polynomial algebra remains hidden in that step.
-/

namespace GppNumberGibbsQuadraticCurvatureSquareBridge

open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticCurvatureAlgebra

/-- Normalized countable Gibbs expectation of a pointwise square. -/
noncomputable def normalizedWeightedSquare
    (β η : ℝ) (f : ℕ → ℝ) : ℝ :=
  (∑' n : ℕ, numberGibbsWeight β η n * (f n) ^ 2) / Z β η

/-- Every normalized weighted square is nonnegative on the confined domain.
This needs no finite truncation: it is the actual countable Gibbs `tsum`. -/
theorem normalizedWeightedSquare_nonneg
    (β : ℝ) {η : ℝ} (hη : 0 < η) (f : ℕ → ℝ) :
    0 ≤ normalizedWeightedSquare β η f := by
  unfold normalizedWeightedSquare
  apply div_nonneg
  · exact tsum_nonneg (fun n =>
      mul_nonneg (numberGibbsWeight_nonneg β η n) (sq_nonneg (f n)))
  · exact (Z_pos β hη).le

/-- Centered log-energy observable for the actual quadratic number gas. -/
noncomputable def centeredLogEnergy (β η : ℝ) (n : ℕ) : ℝ :=
  numberLogEnergy n - internalEnergy β η

/-- Denominator-cleared cubic residual evaluated on the actual centered
log-energy observable.  Its coefficients are the exact symbolic coefficients
used in the certified Schur-complement identity. -/
noncomputable def cubicResidualValue
    (β η m2 m3 m4 m5 : ℝ) (n : ℕ) : ℝ :=
  let y := centeredLogEnergy β η n
  metricDet m2 m3 m4 * y ^ 3
    + residualC2 m2 m3 m4 m5 * y ^ 2
    + residualC1 m2 m3 m4 m5 * y
    + residualC0 m2 m3 m4 m5

/-- Exact sixth-order polynomial expansion of the denominator-cleared cubic
residual square.  This is the finite algebra needed before distributing the
countable Gibbs `tsum`; after centering, the linear term has zero expectation. -/
theorem cubicResidual_square_expansion
    (m2 m3 m4 m5 y : ℝ) :
    let D := metricDet m2 m3 m4
    let A := residualC0 m2 m3 m4 m5
    let B := residualC1 m2 m3 m4 m5
    let C := residualC2 m2 m3 m4 m5
    (D * y ^ 3 + C * y ^ 2 + B * y + A) ^ 2 =
      A ^ 2
        + (2 * A * B) * y
        + (B ^ 2 + 2 * A * C) * y ^ 2
        + (2 * A * D + 2 * B * C) * y ^ 3
        + (C ^ 2 + 2 * B * D) * y ^ 4
        + (2 * C * D) * y ^ 5
        + D ^ 2 * y ^ 6 := by
  dsimp
  ring

/-- Substituting a centered moment functional into the exact cubic-square
expansion recovers precisely the symbolic residual square moment.  The first
centered moment is zero, so only `m₂,...,m₆` survive. -/
theorem cubicResidual_centeredMoment_expansion
    (m2 m3 m4 m5 m6 : ℝ) :
    let D := metricDet m2 m3 m4
    let A := residualC0 m2 m3 m4 m5
    let B := residualC1 m2 m3 m4 m5
    let C := residualC2 m2 m3 m4 m5
    A ^ 2
        + (2 * A * B) * 0
        + (B ^ 2 + 2 * A * C) * m2
        + (2 * A * D + 2 * B * C) * m3
        + (C ^ 2 + 2 * B * D) * m4
        + (2 * C * D) * m5
        + D ^ 2 * m6 =
      residualSqMoment m2 m3 m4 m5 m6 := by
  unfold residualSqMoment
  dsimp
  ring

/-- The actual countable normalized Gibbs expectation of the cubic residual
square is nonnegative for arbitrary real moment parameters.  The curvature
application will instantiate those parameters with the actual centered moments. -/
theorem normalized_cubicResidualSquare_nonneg
    (β : ℝ) {η : ℝ} (hη : 0 < η)
    (m2 m3 m4 m5 : ℝ) :
    0 ≤ normalizedWeightedSquare β η
      (cubicResidualValue β η m2 m3 m4 m5) := by
  exact normalizedWeightedSquare_nonneg β hη _

end GppNumberGibbsQuadraticCurvatureSquareBridge

#print axioms GppNumberGibbsQuadraticCurvatureSquareBridge.normalizedWeightedSquare_nonneg
#print axioms GppNumberGibbsQuadraticCurvatureSquareBridge.cubicResidual_square_expansion
#print axioms GppNumberGibbsQuadraticCurvatureSquareBridge.cubicResidual_centeredMoment_expansion
#print axioms GppNumberGibbsQuadraticCurvatureSquareBridge.normalized_cubicResidualSquare_nonneg