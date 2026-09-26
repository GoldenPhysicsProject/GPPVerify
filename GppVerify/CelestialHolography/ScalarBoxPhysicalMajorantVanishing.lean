import GppVerify.CelestialHolography.ScalarBoxSpecialRemainderVanishing
import GppVerify.CelestialHolography.ScalarBoxRegulatorVanishing
import Mathlib.Tactic

/-!
# Vanishing physical scalar-box core majorant

The regulated scalar-box core error is controlled by three already-certified analytic
pieces: the lower-endpoint log-square error, the pole-endpoint log-square error, and the
six-term special-function remainder.  This file packages their sum as the single
majorant needed by the final convergence squeeze.
-/

namespace GppScalarBoxPhysicalMajorantVanishing

open Filter Set
open scoped Topology
open GppScalarBoxLogSquareRemainder
open GppScalarBoxRegulatorVanishing
open GppScalarBoxSpecialFunctionRemainder
open GppScalarBoxSpecialRemainderVanishing

/-- Explicit physical core majorant after `δ=4m/U`, `η=m/S`. -/
noncomputable def physicalCoreMajorant (S U m : ℝ) : ℝ :=
  lowerLogError (4 * m / U) (m / S) *
      (2 * |Real.log (m / U)| + lowerLogError (4 * m / U) (m / S))
    + poleLogError (4 * m / U) (m / S) *
      (2 * |Real.log (m / S)| + poleLogError (4 * m / U) (m / S))
    + specialRemainderMajorant (m / U) (m / S)

/-- For fixed positive kinematic scales, the complete physical core majorant vanishes
from the positive-regulator side. -/
theorem tendsto_physicalCoreMajorant_nhdsGT_zero
    {S U : ℝ} (hS : 0 < S) (hU : 0 < U) :
    Tendsto (physicalCoreMajorant S U) (𝓝[>] 0) (𝓝 0) := by
  have hlower := tendsto_lower_log_square_majorant hS hU
  have hpole := tendsto_pole_log_square_majorant hS hU
  have hspecial := tendsto_specialRemainderMajorant_regulator hS hU
  have h := (hlower.add hpole).add hspecial
  simpa [physicalCoreMajorant] using h

end GppScalarBoxPhysicalMajorantVanishing

#print axioms GppScalarBoxPhysicalMajorantVanishing.tendsto_physicalCoreMajorant_nhdsGT_zero
