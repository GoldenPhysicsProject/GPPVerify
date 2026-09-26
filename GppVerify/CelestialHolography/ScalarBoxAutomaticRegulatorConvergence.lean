import GppVerify.CelestialHolography.PositiveRegulatorEventuallySmall
import GppVerify.CelestialHolography.ScalarBoxStructuredPhysicalConvergence

/-!
# Scalar-box convergence with automatic small-regulator bounds

The structured physical scalar-box convergence theorem historically exposed two
small-regulator assumptions,

  m ≤ S/4,    m ≤ U/16,

as explicit eventual hypotheses.  For fixed positive `S,U` these are automatic as
`m → 0⁺`.  This wrapper removes those two bookkeeping assumptions while leaving the
actual physical chamber and defining-relation hypotheses unchanged.
-/

namespace GppScalarBoxAutomaticRegulatorConvergence

open Filter Set
open scoped Topology
open GppPositiveRegulatorEventuallySmall
open GppScalarBoxStructuredPhysicalConvergence
open GppScalarBoxPhysicalCoreBound
open GppScalarBoxSpecialFunctionRemainder

/-- Full structured scalar-box one-sided regulator convergence with the elementary
small-`m` bounds generated automatically from `S>0` and `U>0`. -/
theorem tendsto_physical_structured_scalarBox_core_zero_auto_small
    {S U : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    {R κ q a t ρ η B x δ : ℝ → ℝ}
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
  exact tendsto_physical_structured_scalarBox_core_zero
    hS hU
    (eventually_le_quarter hS)
    (eventually_le_sixteenth hU)
    hRlo hRhi hκlo hκhi hxlo hxhi hq ha hRsq hκsq hρ hη hδ ht hBdef
    hκsqScale hxsq hRsqScale

end GppScalarBoxAutomaticRegulatorConvergence

#print axioms GppScalarBoxAutomaticRegulatorConvergence.tendsto_physical_structured_scalarBox_core_zero_auto_small
