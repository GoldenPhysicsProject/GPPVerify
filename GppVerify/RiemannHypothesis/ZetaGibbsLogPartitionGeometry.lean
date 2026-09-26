import GppVerify.RiemannHypothesis.ZetaGibbsThermodynamicDerivatives
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# Log-partition Hessian and Fisher geometry of the zeta Gibbs family

On the honest thermodynamic half-line `β > 1`, the project already proves

  A'(β) = -U(β),   U'(β) = -g(β),

where `A = log Z`, `U` is the mean log-energy, and `g` is the Gibbs Fisher
metric coefficient, equal to the log-energy variance.  This file packages the
composition as the exact one-dimensional Hessian/Fisher identity.
-/

namespace GppZetaGibbsLogPartitionGeometry

open GppZetaGibbsFisher
open GppZetaGibbsThermodynamicDerivatives

/-- The first-response field of the log-partition potential. -/
noncomputable def logPartitionSlope (β : ℝ) : ℝ := -zetaMeanEnergy β

/-- The packaged slope is exactly the derivative of `A = log Z`. -/
theorem logPartitionSlope_eq_deriv
    {β : ℝ} (hβ : 1 < β) :
    logPartitionSlope β = deriv zetaLogPartition β := by
  rw [(hasDerivAt_zetaLogPartition hβ).deriv]
  rfl

/-- **Fisher-Hessian law.** The derivative of the log-partition slope is the
Gibbs Fisher metric coefficient, i.e. the log-energy variance. Equivalently,
`A''(β) = Var_β(log n)` on `β > 1`. -/
theorem hasDerivAt_logPartitionSlope
    {β : ℝ} (hβ : 1 < β) :
    HasDerivAt logPartitionSlope (logEnergyVariance β) β := by
  have h := (hasDerivAt_zetaMeanEnergy hβ).neg
  simpa [logPartitionSlope] using h

/-- The Hessian/Fisher response is nonnegative on the honest Gibbs domain. -/
theorem deriv_logPartitionSlope_nonneg
    {β : ℝ} (hβ : 1 < β) :
    0 ≤ deriv logPartitionSlope β := by
  rw [(hasDerivAt_logPartitionSlope hβ).deriv]
  exact logEnergyVariance_nonneg hβ

end GppZetaGibbsLogPartitionGeometry

#print axioms GppZetaGibbsLogPartitionGeometry.logPartitionSlope_eq_deriv
#print axioms GppZetaGibbsLogPartitionGeometry.hasDerivAt_logPartitionSlope
#print axioms GppZetaGibbsLogPartitionGeometry.deriv_logPartitionSlope_nonneg
