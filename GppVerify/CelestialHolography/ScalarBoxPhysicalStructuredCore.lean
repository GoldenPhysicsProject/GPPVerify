import GppVerify.CelestialHolography.ScalarBoxStructuredRemainder
import GppVerify.CelestialHolography.ScalarBoxPhysicalSpecialRemainder
import GppVerify.CelestialHolography.ScalarBoxD0PrefactorVanishing
import Mathlib.Tactic

/-!
# Exact physical scalar-box moving core

After the branch-free reciprocal-dilogarithm reduction, the moving scalar-box core has
an elementary logarithmic part plus the already isolated six-term special remainder.
This file identifies the massless logarithmic model exactly with `scalarBoxD0` and
propagates the certified endpoint errors through that exact core.
-/

namespace GppScalarBoxPhysicalStructuredCore

open GppScalarBoxStructuredRemainder
open GppScalarBoxPhysicalSpecialRemainder
open GppScalarBoxSpecialFunctionRemainder
open GppScalarBoxD0PrefactorVanishing

/-- The transformed moving core of the internally regulated scalar box. -/
noncomputable def scalarBoxMovingCore (a q t : ℝ) : ℝ :=
  Real.log a * Real.log t + (1 / 2 : ℝ) * (Real.log a) ^ 2
    - Real.pi ^ 2 / 6 + specialRemainder a q t

/-- The natural logarithmic scale model is exactly the explicit massless core. -/
theorem scalarBoxD0_eq_log_scale_core
    {S U m : ℝ} (hS : 0 < S) (hU : 0 < U) (hm : 0 < m) :
    scalarBoxD0 S U m =
      Real.log (m / U) * Real.log (m / S) +
        (1 / 2 : ℝ) * (Real.log (m / U)) ^ 2 - Real.pi ^ 2 / 6 := by
  rw [Real.log_div hm.ne' hU.ne', Real.log_div hm.ne' hS.ne']
  unfold scalarBoxD0
  ring

/-- Exact structured bound for the transformed moving core.  This theorem is the
non-tautological bridge from the endpoint logarithmic estimates and the six-term
special remainder to the physical core difference. -/
theorem abs_movingCore_sub_D0_le
    {S U m a q t A B Estar : ℝ}
    (hS : 0 < S) (hU : 0 < U) (hm : 0 < m)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hE0 : 0 ≤ Estar)
    (ha : |Real.log a - Real.log (m / U)| ≤ A)
    (ht : |Real.log t - Real.log (m / S)| ≤ B)
    (hE : |specialRemainder a q t| ≤ Estar) :
    |scalarBoxMovingCore a q t - scalarBoxD0 S U m| ≤
      A * (|Real.log (m / S)| + |Real.log (m / U)|) +
        |Real.log (m / U)| * B + A * B +
          (1 / 2 : ℝ) * A ^ 2 + Estar := by
  have hbase := abs_structured_core_difference_le
    (ellU := Real.log (m / U)) (ellS := Real.log (m / S))
    (da := Real.log a - Real.log (m / U))
    (dt := Real.log t - Real.log (m / S))
    (E := specialRemainder a q t)
    (A := A) (B := B) (Estar := Estar)
    (c := -Real.pi ^ 2 / 6)
    hA0 hB0 hE0 ha ht hE
  rw [scalarBoxD0_eq_log_scale_core hS hU hm]
  unfold scalarBoxMovingCore
  convert hbase using 1 <;> ring

end GppScalarBoxPhysicalStructuredCore

#print axioms GppScalarBoxPhysicalStructuredCore.scalarBoxD0_eq_log_scale_core
#print axioms GppScalarBoxPhysicalStructuredCore.abs_movingCore_sub_D0_le
