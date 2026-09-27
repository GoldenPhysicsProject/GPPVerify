import GppVerify.RiemannHypothesis.NumberGibbsQuadraticPartitionDerivatives
import Mathlib.Tactic

/-!
# Differential Massieu laws for the quadratically confined number Gibbs family

The countable partition-function derivatives are now certified in both parameters.
Since `Z > 0` throughout the confined domain `η > 0`, composition with the real
logarithm gives the exact normalized thermodynamic response laws

  ∂β log Z = -M1 / Z,
  ∂η log Z = -M2 / Z.

These are the first-gradient identities underlying the covariance/Fisher Hessian.
-/

namespace GppNumberGibbsQuadraticMassieuDerivatives

open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticPartitionDerivatives

/-- The inverse-temperature derivative of the Massieu potential is minus the
normalized first logarithmic moment. -/
theorem hasDerivAt_logZ_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt
      (fun b : ℝ => Real.log (Z b η))
      (-internalEnergy β η) β := by
  have hZne : Z β η ≠ 0 := ne_of_gt (Z_pos β hη)
  have hlog : HasDerivAt Real.log (1 / Z β η) (Z β η) := by
    simpa [one_div] using Real.hasDerivAt_log hZne
  have H := hlog.comp β (hasDerivAt_Z_beta β hη)
  simpa [Function.comp_apply, internalEnergy, div_eq_mul_inv, mul_comm] using H

/-- The confinement derivative of the Massieu potential is minus the normalized
second logarithmic moment. -/
theorem hasDerivAt_logZ_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt
      (fun e : ℝ => Real.log (Z β e))
      (-quadraticEnergy β η) η := by
  have hZne : Z β η ≠ 0 := ne_of_gt (Z_pos β hη)
  have hlog : HasDerivAt Real.log (1 / Z β η) (Z β η) := by
    simpa [one_div] using Real.hasDerivAt_log hZne
  have H := hlog.comp η (hasDerivAt_Z_eta β hη)
  simpa [Function.comp_apply, quadraticEnergy, div_eq_mul_inv, mul_comm] using H

end GppNumberGibbsQuadraticMassieuDerivatives

#print axioms GppNumberGibbsQuadraticMassieuDerivatives.hasDerivAt_logZ_beta
#print axioms GppNumberGibbsQuadraticMassieuDerivatives.hasDerivAt_logZ_eta
