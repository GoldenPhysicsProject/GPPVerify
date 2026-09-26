import GppVerify.CelestialHolography.ScalarBoxPhysicalMajorantVanishing
import GppVerify.CelestialHolography.ScalarBoxD0PrefactorVanishing
import GppVerify.CelestialHolography.ScalarBoxConvergenceAssembly
import Mathlib.Tactic

/-!
# Physical scalar-box convergence from the core bound

At this layer every analytic limit has already been discharged.  The only remaining
input is the eventual physical estimate of the moving scalar-box core by the explicit
majorant `physicalCoreMajorant`.
-/

namespace GppScalarBoxPhysicalConvergence

open Filter Set
open scoped Topology
open GppScalarBoxPhysicalMajorantVanishing
open GppScalarBoxD0PrefactorVanishing
open GppScalarBoxConvergenceAssembly
open GppScalarBoxPrefactorRemainder

/-- Final physical convergence assembly.  Once the unprefactored moving core `D` is
bounded by `physicalCoreMajorant`, the exact quadratic relation for `κ` controls the
inverse prefactor and the complete corrected remainder tends to zero.

The hypotheses `m ≤ S` and `1 ≤ κ` are stated eventually because this theorem is the
interface between the pointwise physical chamber and the one-sided regulator limit. -/
theorem tendsto_corrected_scalarBox_core_zero_of_physical_core_bound
    {S U : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    {D κ : ℝ → ℝ}
    (hmS : ∀ᶠ m in 𝓝[>] 0, m ≤ S)
    (hκ : ∀ᶠ m in 𝓝[>] 0, 1 ≤ κ m)
    (hκsq : ∀ᶠ m in 𝓝[>] 0,
      (κ m) ^ 2 = 1 + 4 * m * (S - m) / (S * U))
    (hcore : ∀ᶠ m in 𝓝[>] 0,
      |D m - scalarBoxD0 S U m| ≤ physicalCoreMajorant S U m) :
    Tendsto
      (fun m : ℝ => D m / κ m - scalarBoxD0 S U m)
      (𝓝[>] 0) (𝓝 0) := by
  have hM := tendsto_physicalCoreMajorant_nhdsGT_zero hS hU
  have hP := tendsto_delta_half_mul_abs_scalarBoxD0_nhdsGT_zero (S := S) hU
  have hbound : ∀ᶠ m in 𝓝[>] 0,
      |D m / κ m - scalarBoxD0 S U m| ≤
        physicalCoreMajorant S U m +
          ((4 * m / U) / 2) * |scalarBoxD0 S U m| := by
    filter_upwards [self_mem_nhdsWithin, hmS, hκ, hκsq, hcore] with m hm hmS' hκ' hκsq' hcore'
    exact abs_prefactor_remainder_le_of_physical_core_bound
      hS hU hm.le hmS' hκ' hκsq' hcore'
  exact tendsto_corrected_remainder_zero_of_prefactor_bound hM hP hbound

end GppScalarBoxPhysicalConvergence

#print axioms GppScalarBoxPhysicalConvergence.tendsto_corrected_scalarBox_core_zero_of_physical_core_bound
