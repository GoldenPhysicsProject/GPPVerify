import GppVerify.CelestialHolography.ScalarBoxPrefactorRemainder
import Mathlib.Tactic

/-!
# Final scalar-box convergence assembly

This file isolates the last topological step in the regulated scalar-box argument.
Once a nonnegative envelope for the prefactor-corrected remainder is known to vanish,
the remainder itself vanishes by the order squeeze theorem.  The physical endpoint and
special-function estimates are supplied by the preceding scalar-box files.
-/

namespace GppScalarBoxConvergenceAssembly

open Filter Set
open scoped Topology

/-- Abstract final squeeze: if the core majorant and the prefactor contamination both
vanish, and their sum bounds the absolute corrected remainder eventually, then the
corrected remainder tends to zero. -/
theorem tendsto_corrected_remainder_zero
    {D D0 κ M P : ℝ → ℝ}
    (hM : Tendsto M (𝓝[>] 0) (𝓝 0))
    (hP : Tendsto P (𝓝[>] 0) (𝓝 0))
    (hbound : ∀ᶠ m in 𝓝[>] 0,
      |D m / κ m - D0 m| ≤ M m + P m) :
    Tendsto (fun m : ℝ => D m / κ m - D0 m) (𝓝[>] 0) (𝓝 0) := by
  have hmajor : Tendsto (fun m : ℝ => M m + P m) (𝓝[>] 0) (𝓝 0) := by
    simpa using hM.add hP
  have hminor : Tendsto (fun m : ℝ => -(M m + P m)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hmajor.neg
  have hlower : ∀ᶠ m in 𝓝[>] 0,
      -(M m + P m) ≤ D m / κ m - D0 m := by
    filter_upwards [hbound] with m hm
    exact (abs_le.mp hm).1
  have hupper : ∀ᶠ m in 𝓝[>] 0,
      D m / κ m - D0 m ≤ M m + P m := by
    filter_upwards [hbound] with m hm
    exact (abs_le.mp hm).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hminor hmajor hlower hupper

/-- Convenient specialization to the exact prefactor envelope proved in
`ScalarBoxPrefactorRemainder`: if the structured core error vanishes and
`(δ/2)|D0|` vanishes, then the prefactor-corrected remainder vanishes. -/
theorem tendsto_corrected_remainder_zero_of_prefactor_bound
    {D D0 κ δ M : ℝ → ℝ}
    (hM : Tendsto M (𝓝[>] 0) (𝓝 0))
    (hP : Tendsto (fun m : ℝ => (δ m / 2) * |D0 m|) (𝓝[>] 0) (𝓝 0))
    (hbound : ∀ᶠ m in 𝓝[>] 0,
      |D m / κ m - D0 m| ≤ M m + (δ m / 2) * |D0 m|) :
    Tendsto (fun m : ℝ => D m / κ m - D0 m) (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_corrected_remainder_zero hM hP hbound

end GppScalarBoxConvergenceAssembly

#print axioms GppScalarBoxConvergenceAssembly.tendsto_corrected_remainder_zero
#print axioms GppScalarBoxConvergenceAssembly.tendsto_corrected_remainder_zero_of_prefactor_bound
