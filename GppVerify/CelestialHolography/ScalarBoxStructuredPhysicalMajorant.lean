import GppVerify.CelestialHolography.ScalarBoxStructuredRemainder
import GppVerify.CelestialHolography.ScalarBoxPhysicalSpecialRemainder
import GppVerify.CelestialHolography.ScalarBoxSpecialRemainderVanishing
import GppVerify.CelestialHolography.ScalarBoxRegulatorVanishing
import GppVerify.CelestialHolography.ScalarBoxD0PrefactorVanishing
import Mathlib.Tactic

/-!
# Correct structured physical majorant for the scalar-box core

The exact moving core after the dilogarithm identities is

  log(a) log(t) + 1/2 log(a)^2 - pi^2/6 + E.

Its massless scale model is obtained by replacing `log a` with `log(m/U)` and
`log t` with `log(m/S)`.  Because the core contains a mixed product, the natural
majorant is the five-term structured bound from `ScalarBoxStructuredRemainder`,
not a sum of two independent square-error bounds.
-/

namespace GppScalarBoxStructuredPhysicalMajorant

open Filter Set
open scoped Topology
open GppScalarBoxStructuredRemainder
open GppScalarBoxLogSquareRemainder
open GppScalarBoxRegulatorVanishing
open GppScalarBoxSpecialFunctionRemainder
open GppScalarBoxD0PrefactorVanishing

/-- The exact unprefactored regulated scalar-box core after branch-free reduction. -/
noncomputable def structuredScalarBoxCore (a t E : ℝ) : ℝ :=
  Real.log a * Real.log t + (1 / 2 : ℝ) * (Real.log a) ^ 2 - Real.pi ^ 2 / 6 + E

/-- The massless core is exactly the natural logarithmic scale model. -/
theorem scalarBoxD0_eq_scale_core
    {S U m : ℝ} (hS : 0 < S) (hU : 0 < U) (hm : 0 < m) :
    scalarBoxD0 S U m =
      Real.log (m / U) * Real.log (m / S) +
        (1 / 2 : ℝ) * (Real.log (m / U)) ^ 2 - Real.pi ^ 2 / 6 := by
  rw [Real.log_div hm.ne' hU.ne', Real.log_div hm.ne' hS.ne']
  unfold scalarBoxD0
  ring

/-- Correct five-term physical majorant for the mixed-logarithm core. -/
noncomputable def structuredPhysicalCoreMajorant (S U m : ℝ) : ℝ :=
  let Ea := lowerLogError (4 * m / U) (m / S)
  let Et := poleLogError (4 * m / U) (m / S)
  Ea * (|Real.log (m / S)| + |Real.log (m / U)|)
    + |Real.log (m / U)| * Et
    + Ea * Et
    + (1 / 2 : ℝ) * Ea ^ 2
    + specialRemainderMajorant (m / U) (m / S)

/-- Pointwise structured core estimate from the three certified interfaces:
logarithmic control of `a`, logarithmic control of `t`, and the special remainder. -/
theorem abs_structuredScalarBoxCore_sub_D0_le
    {S U m a t E : ℝ}
    (hS : 0 < S) (hU : 0 < U) (hm : 0 < m)
    (ha : |Real.log a - Real.log (m / U)| ≤
      lowerLogError (4 * m / U) (m / S))
    (ht : |Real.log t - Real.log (m / S)| ≤
      poleLogError (4 * m / U) (m / S))
    (hE : |E| ≤ specialRemainderMajorant (m / U) (m / S)) :
    |structuredScalarBoxCore a t E - scalarBoxD0 S U m| ≤
      structuredPhysicalCoreMajorant S U m := by
  have hδ0 : 0 ≤ 4 * m / U := by positivity
  have hη0 : 0 ≤ m / S := by positivity
  rcases logError_nonneg hδ0 hη0 with ⟨hEa0, hEt0⟩
  have hEstar0 : 0 ≤ specialRemainderMajorant (m / U) (m / S) := by
    unfold specialRemainderMajorant
    positivity
  have hbound := abs_structured_core_difference_le
    (ellU := Real.log (m / U)) (ellS := Real.log (m / S))
    (da := Real.log a - Real.log (m / U))
    (dt := Real.log t - Real.log (m / S))
    (E := E)
    (A := lowerLogError (4 * m / U) (m / S))
    (B := poleLogError (4 * m / U) (m / S))
    (Estar := specialRemainderMajorant (m / U) (m / S))
    (c := -Real.pi ^ 2 / 6)
    hEa0 hEt0 hEstar0 ha ht hE
  rw [scalarBoxD0_eq_scale_core hS hU hm]
  unfold structuredScalarBoxCore structuredPhysicalCoreMajorant
  dsimp
  convert hbound using 1 <;> ring

/-- For fixed positive kinematic scales, the correct mixed-logarithm majorant vanishes
from the positive-regulator side. -/
theorem tendsto_structuredPhysicalCoreMajorant_nhdsGT_zero
    {S U : ℝ} (hS : 0 < S) (hU : 0 < U) :
    Tendsto (structuredPhysicalCoreMajorant S U) (𝓝[>] 0) (𝓝 0) := by
  let A : ℝ := (289 / 192 : ℝ) * (1 / S + (33 / 16 : ℝ) * (1 / U))
  let B : ℝ := (103 / 17 : ℝ) * (1 / U) + (4 / 3 : ℝ) * (1 / S)
  let C : ℝ := 4 / (3 * S * U)
  have hm : Tendsto (fun m : ℝ => m) (𝓝[>] 0) (𝓝 0) :=
    (continuousAt_id.tendsto).mono_left inf_le_left
  have hm2 : Tendsto (fun m : ℝ => m ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using hm.pow 2
  have hEa : Tendsto (fun m : ℝ => A * m) (𝓝[>] 0) (𝓝 0) := by
    simpa using hm.const_mul A
  have hEt : Tendsto (fun m : ℝ => B * m + C * m ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hm.const_mul B).add (hm2.const_mul C)
  have hEaLogS :
      Tendsto (fun m : ℝ => (A * m) * |Real.log (m / S)|) (𝓝[>] 0) (𝓝 0) := by
    simpa [mul_assoc] using (tendsto_mul_abs_log_div_const_nhdsGT_zero hS).const_mul A
  have hEaLogU :
      Tendsto (fun m : ℝ => (A * m) * |Real.log (m / U)|) (𝓝[>] 0) (𝓝 0) := by
    simpa [mul_assoc] using (tendsto_mul_abs_log_div_const_nhdsGT_zero hU).const_mul A
  have hEtLogU :
      Tendsto
        (fun m : ℝ => |Real.log (m / U)| * (B * m + C * m ^ 2))
        (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun k : ℝ => B * (k * |Real.log (k / U)|))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_mul_abs_log_div_const_nhdsGT_zero hU).const_mul B
    have h2 : Tendsto (fun k : ℝ => C * (k ^ 2 * |Real.log (k / U)|))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_sq_mul_abs_log_div_const_nhdsGT_zero hU).const_mul C
    have h : Tendsto
        (fun x : ℝ => B * (x * |Real.log (x / U)|) + C * (x ^ 2 * |Real.log (x / U)|))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using h1.add h2
    apply h.congr'
    filter_upwards with m
    ring
  have hEaEt : Tendsto (fun x : ℝ => A * x * (B * x + C * x ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hEa.mul hEt
  have hEaSq : Tendsto (fun x : ℝ => (A * x) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using hEa.pow 2
  have hspecial :=
    GppScalarBoxSpecialRemainderVanishing.tendsto_specialRemainderMajorant_regulator hS hU
  have hsum : Tendsto
      (fun x : ℝ =>
        A * x * |Real.log (x / S)| + A * x * |Real.log (x / U)| +
          |Real.log (x / U)| * (B * x + C * x ^ 2) +
          A * x * (B * x + C * x ^ 2) +
          (1 / 2 : ℝ) * (A * x) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (((hEaLogS.add hEaLogU).add hEtLogU).add hEaEt).add
      (hEaSq.const_mul (1 / 2 : ℝ))
  have hall : Tendsto
      (fun x : ℝ =>
        A * x * |Real.log (x / S)| + A * x * |Real.log (x / U)| +
          |Real.log (x / U)| * (B * x + C * x ^ 2) +
          A * x * (B * x + C * x ^ 2) +
          (1 / 2 : ℝ) * (A * x) ^ 2 +
          specialRemainderMajorant (x / U) (x / S))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hsum.add hspecial
  apply hall.congr'
  filter_upwards with m
  unfold structuredPhysicalCoreMajorant
  dsimp
  rw [lowerLogError_regulator_polynomial hS.ne' hU.ne']
  rw [poleLogError_regulator_polynomial hS.ne' hU.ne']
  dsimp [A, B, C]
  ring

end GppScalarBoxStructuredPhysicalMajorant

#print axioms GppScalarBoxStructuredPhysicalMajorant.scalarBoxD0_eq_scale_core
#print axioms GppScalarBoxStructuredPhysicalMajorant.abs_structuredScalarBoxCore_sub_D0_le
#print axioms GppScalarBoxStructuredPhysicalMajorant.tendsto_structuredPhysicalCoreMajorant_nhdsGT_zero
