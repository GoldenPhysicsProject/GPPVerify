import GppVerify.CelestialHolography.ScalarBoxSpecialFunctionRemainder
import GppVerify.CelestialHolography.ScalarBoxRegulatorVanishing
import Mathlib.Tactic

/-!
# Vanishing of the explicit scalar-box special-function majorant

This closes the analytic limit of the six-term special-function remainder majorant
`E_*` after the physical substitutions `ρ=m/U` and `η=m/S`.
-/

namespace GppScalarBoxSpecialRemainderVanishing

open Filter Set
open scoped Topology
open GppScalarBoxSpecialFunctionRemainder
open GppScalarBoxRegulatorVanishing

/-- The dimensionless special-function majorant tends to zero for fixed positive
kinematic scales `S,U`. -/
theorem tendsto_specialRemainderMajorant_regulator
    {S U : ℝ} (hS : 0 < S) (hU : 0 < U) :
    Tendsto
      (fun m : ℝ => specialRemainderMajorant (m / U) (m / S))
      (𝓝[>] 0) (𝓝 0) := by
  have hm : Tendsto (fun m : ℝ => m) (𝓝[>] 0) (𝓝 0) := by
    exact (continuousAt_id.tendsto).mono_left inf_le_left
  have hρ : Tendsto (fun m : ℝ => m / U) (𝓝[>] 0) (𝓝 0) := by
    have h := hm.mul_const (1 / U)
    simpa [div_eq_mul_inv] using h
  have hη : Tendsto (fun m : ℝ => m / S) (𝓝[>] 0) (𝓝 0) := by
    have h := hm.mul_const (1 / S)
    simpa [div_eq_mul_inv] using h
  have hρ2 : Tendsto (fun m : ℝ => (m / U) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using hρ.pow 2
  have hρ3 : Tendsto (fun m : ℝ => (m / U) ^ 3) (𝓝[>] 0) (𝓝 0) := by
    simpa using hρ.pow 3
  have hρ2log :
      Tendsto (fun m : ℝ => (m / U) ^ 2 * |Real.log (m / U)|)
        (𝓝[>] 0) (𝓝 0) := by
    have hbase := tendsto_sq_mul_abs_log_div_const_nhdsGT_zero hU
    have h := hbase.const_mul (1 / U ^ 2)
    convert h using 1
    · funext m
      field_simp [hU.ne']
    · norm_num
  have htail :
      Tendsto
        (fun m : ℝ =>
          (m / U) ^ 2 *
            (|Real.log (m / U)| + (81 / 32 : ℝ) * (m / U)))
        (𝓝[>] 0) (𝓝 0) := by
    have h := hρ2log.add (hρ3.const_mul (81 / 32 : ℝ))
    simpa [div_eq_mul_inv, mul_add, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h
  have htotal :=
    (hη.const_mul (48 / 19 : ℝ)).add
      ((hρ.const_mul (232 / 105 : ℝ)).add
        ((hρ2.const_mul ((648 / 289 : ℝ) + (9 / 8 : ℝ))).add
          (htail.const_mul (486 / 289 : ℝ))))
  convert htotal using 1
  · funext m
    unfold specialRemainderMajorant
    ring
  · norm_num

end GppScalarBoxSpecialRemainderVanishing

#print axioms GppScalarBoxSpecialRemainderVanishing.tendsto_specialRemainderMajorant_regulator
