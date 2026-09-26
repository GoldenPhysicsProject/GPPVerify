import GppVerify.RiemannHypothesis.ZetaGibbsCumulantDerivative
import Mathlib.Tactic

/-!
# Differential heat-capacity law for the zeta Gibbs family

The dimensionless heat capacity is

  C(beta) = beta^2 kappa_2(beta),

where `kappa_2` is the log-energy variance.  The already-proved cumulant flow
`kappa_2' = -kappa_3` therefore gives the exact response law

  C'(beta) = 2 beta kappa_2(beta) - beta^2 kappa_3(beta)

throughout the honest Gibbs half-line `beta > 1`.

The two terms compete, so no global sign for `C'` is asserted here.
-/

namespace GppZetaGibbsHeatCapacityDerivative

open GppZetaGibbsFisher
open GppZetaGibbsCumulantDerivative

/-- **Exact heat-capacity flow:** scaling contributes `2 beta kappa_2`, while
third-cumulant skewness contributes `-beta^2 kappa_3`. -/
theorem hasDerivAt_heatCapacity
    {β : ℝ} (hβ : 1 < β) :
    HasDerivAt heatCapacity
      (2 * β * logEnergyVariance β - β ^ 2 * logEnergyThirdCumulant β) β := by
  have hsq0 : HasDerivAt (fun x : ℝ => x * x) (β + β) β := by
    simpa only [id_eq, one_mul, mul_one] using
      (hasDerivAt_id β).mul (hasDerivAt_id β)
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * β) β := by
    convert hsq0 using 1 <;> ring
  have hvar := hasDerivAt_logEnergyVariance hβ
  unfold heatCapacity
  convert hsq.mul hvar using 1 <;> ring

/-- Derivative form of the same thermodynamic identity. -/
theorem deriv_heatCapacity
    {β : ℝ} (hβ : 1 < β) :
    deriv heatCapacity β =
      2 * β * logEnergyVariance β - β ^ 2 * logEnergyThirdCumulant β := by
  exact (hasDerivAt_heatCapacity hβ).deriv

end GppZetaGibbsHeatCapacityDerivative

#print axioms GppZetaGibbsHeatCapacityDerivative.hasDerivAt_heatCapacity
#print axioms GppZetaGibbsHeatCapacityDerivative.deriv_heatCapacity
