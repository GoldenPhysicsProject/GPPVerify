import GppVerify.RiemannHypothesis.ZetaGibbsCumulantHierarchy
import GppVerify.RiemannHypothesis.ZetaGibbsCumulantDerivative
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# Strict curvature of the zeta Gibbs variance response

On the honest Gibbs half-line `beta > 1`, the already-formalized cumulant ladder gives

  kappa_2' = -kappa_3,
  kappa_3' = -kappa_4,
  kappa_4 > 0.

This file packages the immediate exact consequence: the variance slope response
`-kappa_3` has derivative `kappa_4`, hence strictly positive derivative.  This is the
local differential curvature statement required for the fluctuation geometry.  We do
not promote it here to a global `StrictConvexOn` theorem.
-/

namespace GppZetaGibbsVarianceCurvature

open GppZetaGibbsFisher
open GppZetaGibbsCumulantDerivative
open GppZetaGibbsFourthCumulant
open GppZetaGibbsCumulantHierarchy

/-- The exact slope of the variance response on the honest Gibbs domain. -/
noncomputable def varianceSlope (β : ℝ) : ℝ :=
  -logEnergyThirdCumulant β

/-- The packaged variance slope is exactly the derivative of the genuine Gibbs variance. -/
theorem varianceSlope_eq_deriv_variance
    {β : ℝ} (hβ : 1 < β) :
    varianceSlope β = deriv logEnergyVariance β := by
  rw [(hasDerivAt_logEnergyVariance hβ).deriv]
  rfl

/-- **Exact fluctuation-curvature law**: the beta derivative of the variance slope is
`kappa_4`. Equivalently, at the response level, `kappa_2'' = kappa_4`. -/
theorem hasDerivAt_varianceSlope
    {β : ℝ} (hβ : 1 < β) :
    HasDerivAt varianceSlope (logEnergyFourthCumulant β) β := by
  have h := (hasDerivAt_logEnergyThirdCumulant_eq_neg_fourth hβ).neg
  simpa [varianceSlope] using h

/-- The fluctuation curvature is strictly positive throughout `beta > 1`. -/
theorem deriv_varianceSlope_pos
    {β : ℝ} (hβ : 1 < β) :
    0 < deriv varianceSlope β := by
  rw [(hasDerivAt_varianceSlope hβ).deriv]
  exact logEnergyFourthCumulant_pos hβ

end GppZetaGibbsVarianceCurvature

#print axioms GppZetaGibbsVarianceCurvature.varianceSlope_eq_deriv_variance
#print axioms GppZetaGibbsVarianceCurvature.hasDerivAt_varianceSlope
#print axioms GppZetaGibbsVarianceCurvature.deriv_varianceSlope_pos
