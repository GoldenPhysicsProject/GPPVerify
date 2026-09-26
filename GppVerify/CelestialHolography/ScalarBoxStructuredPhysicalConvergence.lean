import GppVerify.CelestialHolography.ScalarBoxStructuredPhysicalMajorant
import GppVerify.CelestialHolography.ScalarBoxD0PrefactorVanishing
import GppVerify.CelestialHolography.ScalarBoxConvergenceAssembly
import GppVerify.CelestialHolography.ScalarBoxPrefactorRemainder
import GppVerify.CelestialHolography.ScalarBoxPhysicalCoreBound
import Mathlib.Tactic

/-!
# Structured physical scalar-box convergence

This is the convergence assembly for the correct mixed-logarithm majorant.  Once the
moving core is bounded by `structuredPhysicalCoreMajorant`, every remaining term is
already known to vanish and the physical `1/kappa` prefactor is controlled by its exact
quadratic defining relation.
-/

namespace GppScalarBoxStructuredPhysicalConvergence

open Filter Set
open scoped Topology
open GppScalarBoxStructuredPhysicalMajorant
open GppScalarBoxD0PrefactorVanishing
open GppScalarBoxConvergenceAssembly
open GppScalarBoxPrefactorRemainder
open GppScalarBoxPhysicalCoreBound
open GppScalarBoxSpecialFunctionRemainder

/-- Final convergence assembly for the correct structured scalar-box core bound. -/
theorem tendsto_corrected_scalarBox_core_zero_of_structured_bound
    {S U : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    {D κ : ℝ → ℝ}
    (hmS : ∀ᶠ m in 𝓝[>] 0, m ≤ S)
    (hκ : ∀ᶠ m in 𝓝[>] 0, 1 ≤ κ m)
    (hκsq : ∀ᶠ m in 𝓝[>] 0,
      (κ m) ^ 2 = 1 + 4 * m * (S - m) / (S * U))
    (hcore : ∀ᶠ m in 𝓝[>] 0,
      |D m - scalarBoxD0 S U m| ≤ structuredPhysicalCoreMajorant S U m) :
    Tendsto
      (fun m : ℝ => D m / κ m - scalarBoxD0 S U m)
      (𝓝[>] 0) (𝓝 0) := by
  have hM := tendsto_structuredPhysicalCoreMajorant_nhdsGT_zero hS hU
  have hP := tendsto_delta_half_mul_abs_scalarBoxD0_nhdsGT_zero (S := S) hU
  have hbound : ∀ᶠ m in 𝓝[>] 0,
      |D m / κ m - scalarBoxD0 S U m| ≤
        structuredPhysicalCoreMajorant S U m +
          ((4 * m / U) / 2) * |scalarBoxD0 S U m| := by
    filter_upwards [self_mem_nhdsWithin, hmS, hκ, hκsq, hcore] with
      m hm hmS' hκ' hκsq' hcore'
    exact abs_prefactor_remainder_le_of_physical_core_bound
      hS hU hm.le hmS' hκ' hκsq' hcore'
  exact tendsto_corrected_remainder_zero_of_prefactor_bound hM hP hbound

/-- Full one-sided regulator limit for the actual structured scalar-box core, assuming the
standard physical small-regulator chamber and the exact defining relations for the moving
kinematic variables eventually hold.  This composes the pointwise physical-core theorem
with the structured convergence assembly; no independent-square majorant is used. -/
theorem tendsto_physical_structured_scalarBox_core_zero
    {S U : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    {R κ q a t ρ η B x δ : ℝ → ℝ}
    (hmS4 : ∀ᶠ m in 𝓝[>] 0, m ≤ S / 4)
    (hmU16 : ∀ᶠ m in 𝓝[>] 0, m ≤ U / 16)
    (hRlo : ∀ᶠ m in 𝓝[>] 0, 8 / 9 ≤ R m)
    (hRhi : ∀ᶠ m in 𝓝[>] 0, R m ≤ 1)
    (hκlo : ∀ᶠ m in 𝓝[>] 0, 1 ≤ κ m)
    (hκhi : ∀ᶠ m in 𝓝[>] 0, κ m ≤ 9 / 8)
    (hxlo : ∀ᶠ m in 𝓝[>] 0, 15 / 16 ≤ x m)
    (hxhi : ∀ᶠ m in 𝓝[>] 0, x m ≤ 1)
    (hq : ∀ᶠ m in 𝓝[>] 0, q m = (1 - R m) / (1 + R m))
    (ha : ∀ᶠ m in 𝓝[>] 0, a m = (κ m - 1) / (κ m + 1))
    (hRsq : ∀ᶠ m in 𝓝[>] 0, (R m) ^ 2 = U / (U + 4 * m))
    (hκsq : ∀ᶠ m in 𝓝[>] 0,
      (κ m) ^ 2 = 1 + 4 * m * (S - m) / (S * U))
    (hρ : ∀ᶠ m in 𝓝[>] 0, ρ m = m / U)
    (hη : ∀ᶠ m in 𝓝[>] 0, η m = m / S)
    (hδ : ∀ᶠ m in 𝓝[>] 0, δ m = 4 * m / U)
    (ht : ∀ᶠ m in 𝓝[>] 0, t m = η m * B m)
    (hBdef : ∀ᶠ m in 𝓝[>] 0,
      B m = 2 * (1 + κ m) /
        ((1 + δ m) * (1 + x m) * (1 + R m) * (1 - η m)))
    (hκsqScale : ∀ᶠ m in 𝓝[>] 0,
      (κ m) ^ 2 = 1 + δ m * (1 - η m))
    (hxsq : ∀ᶠ m in 𝓝[>] 0,
      (x m) ^ 2 = 1 - δ m * η m / (1 + δ m))
    (hRsqScale : ∀ᶠ m in 𝓝[>] 0,
      (R m) ^ 2 = 1 / (1 + δ m)) :
    Tendsto
      (fun m : ℝ =>
        structuredScalarBoxCore (a m) (t m)
            (specialRemainder (a m) (q m) (t m)) / κ m -
          scalarBoxD0 S U m)
      (𝓝[>] 0) (𝓝 0) := by
  have hmS : ∀ᶠ m in 𝓝[>] 0, m ≤ S := by
    filter_upwards [hmS4] with m hm
    linarith
  have hcore : ∀ᶠ m in 𝓝[>] 0,
      |structuredScalarBoxCore (a m) (t m)
          (specialRemainder (a m) (q m) (t m)) - scalarBoxD0 S U m| ≤
        structuredPhysicalCoreMajorant S U m := by
    filter_upwards [self_mem_nhdsWithin, hmS4, hmU16, hRlo, hRhi, hκlo, hκhi,
      hxlo, hxhi, hq, ha, hRsq, hκsq, hρ, hη, hδ, ht, hBdef, hκsqScale,
      hxsq, hRsqScale] with
      m hm hmS4' hmU16' hRlo' hRhi' hκlo' hκhi' hxlo' hxhi' hq' ha' hRsq'
      hκsq' hρ' hη' hδ' ht' hBdef' hκsqScale' hxsq' hRsqScale'
    exact abs_physical_structured_core_sub_D0_le
      hS hU hm hmS4' hmU16' hRlo' hRhi' hκlo' hκhi' hxlo' hxhi'
      hq' ha' hRsq' hκsq' hρ' hη' hδ' ht' hBdef' hκsqScale' hxsq' hRsqScale'
  exact tendsto_corrected_scalarBox_core_zero_of_structured_bound
    hS hU hmS hκlo hκsq hcore

end GppScalarBoxStructuredPhysicalConvergence

#print axioms GppScalarBoxStructuredPhysicalConvergence.tendsto_corrected_scalarBox_core_zero_of_structured_bound
#print axioms GppScalarBoxStructuredPhysicalConvergence.tendsto_physical_structured_scalarBox_core_zero
