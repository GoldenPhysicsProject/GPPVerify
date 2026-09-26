import GppVerify.CelestialHolography.ScalarBoxRegulatorVanishing
import Mathlib.Tactic

/-!
# Vanishing of the scalar-box massless-core prefactor correction

The remaining prefactor term after the structured scalar-box remainder estimate is

  (delta/2) * |D0|,    delta = 4m/U,

where the massless logarithmic core is

  D0 = (3/2) log^2 m - (log S + 2 log U) log m
       + log U log S + (1/2) log^2 U - pi^2/6.

For fixed positive `S,U`, multiplying by `m` kills every term: the only nontrivial
monomials are `m log^2 m` and `m log m`, both already proved in
`ScalarBoxRegulatorVanishing`.
-/

namespace GppScalarBoxD0PrefactorVanishing

open Filter Set
open scoped Topology
open GppScalarBoxRegulatorVanishing

/-- Explicit massless logarithmic core used in the regulated scalar-box expansion. -/
noncomputable def scalarBoxD0 (S U m : ℝ) : ℝ :=
  (3 / 2 : ℝ) * (Real.log m) ^ 2
    - (Real.log S + 2 * Real.log U) * Real.log m
    + Real.log U * Real.log S
    + (1 / 2 : ℝ) * (Real.log U) ^ 2
    - Real.pi ^ 2 / 6

/-- For fixed scales, the regulator annihilates the explicit logarithmic core. -/
theorem tendsto_mul_scalarBoxD0_nhdsGT_zero (S U : ℝ) :
    Tendsto (fun m : ℝ => m * scalarBoxD0 S U m) (𝓝[>] 0) (𝓝 0) := by
  have hm : Tendsto (fun m : ℝ => m) (𝓝[>] 0) (𝓝 0) :=
    (continuousAt_id.tendsto).mono_left inf_le_left
  have hlog := tendsto_mul_log_nhdsGT_zero
  have hlog2 := tendsto_mul_log_sq_nhdsGT_zero
  have h1 := hlog2.const_mul (3 / 2 : ℝ)
  have h2 := hlog.const_mul (-(Real.log S + 2 * Real.log U))
  have hconst := hm.const_mul
    (Real.log U * Real.log S + (1 / 2 : ℝ) * (Real.log U) ^ 2 - Real.pi ^ 2 / 6)
  have h := (h1.add h2).add hconst
  convert h using 1
  · funext m
    unfold scalarBoxD0
    ring
  · norm_num

/-- Absolute-value form of the massless-core vanishing. -/
theorem tendsto_mul_abs_scalarBoxD0_nhdsGT_zero (S U : ℝ) :
    Tendsto (fun m : ℝ => m * |scalarBoxD0 S U m|) (𝓝[>] 0) (𝓝 0) := by
  have h0 :
      Tendsto (fun m : ℝ => |m * scalarBoxD0 S U m|) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_mul_scalarBoxD0_nhdsGT_zero S U).abs
  apply h0.congr'
  filter_upwards [self_mem_nhdsWithin] with m hm
  rw [abs_mul, abs_of_pos hm]

/-- The exact scalar-box prefactor contribution `(delta/2)|D0|`, with
`delta=4m/U`, tends to zero for every fixed positive `U`. -/
theorem tendsto_delta_half_mul_abs_scalarBoxD0_nhdsGT_zero
    {S U : ℝ} (hU : 0 < U) :
    Tendsto
      (fun m : ℝ => ((4 * m / U) / 2) * |scalarBoxD0 S U m|)
      (𝓝[>] 0) (𝓝 0) := by
  have h0 := (tendsto_mul_abs_scalarBoxD0_nhdsGT_zero S U).const_mul (2 / U)
  have h : Tendsto
      (fun m : ℝ => (2 / U) * (m * |scalarBoxD0 S U m|))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using h0
  convert h using 1
  funext m
  field_simp [hU.ne']
  ring

end GppScalarBoxD0PrefactorVanishing

#print axioms GppScalarBoxD0PrefactorVanishing.tendsto_mul_scalarBoxD0_nhdsGT_zero
#print axioms GppScalarBoxD0PrefactorVanishing.tendsto_mul_abs_scalarBoxD0_nhdsGT_zero
#print axioms GppScalarBoxD0PrefactorVanishing.tendsto_delta_half_mul_abs_scalarBoxD0_nhdsGT_zero
