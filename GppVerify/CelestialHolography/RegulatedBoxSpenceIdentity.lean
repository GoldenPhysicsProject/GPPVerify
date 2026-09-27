import GppVerify.CelestialHolography.RegulatedBoxDilogEndpointContinuity
import GppVerify.CelestialHolography.RegulatedBoxSpenceConstancy
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-!
# The real Spence identity for the regulated-box dilogarithm series

The preceding modules prove:
* endpoint limits of the local dilogarithm series at `0` and `1`;
* exact value `li2Series 1 = pi^2 / 6`;
* derivative cancellation of the Spence combination on `(0,1)`;
* constancy of that combination on `(0,1)`.

This file identifies the constant by approaching `0` from within `(0,1)`. The
logarithmic cross term is handled entirely over the reals: `x log x -> 0` by Mathlib's
continuous extension, while `log(1-x)/x -> -1` follows from the derivative of
`log(1-x)` at zero.
-/

namespace GppRegulatedBoxSpenceIdentity

open Set Filter
open scoped Topology
open GppRegulatedBoxDilogSeries
open GppRegulatedBoxDilogEndpointContinuity
open GppRegulatedBoxSpenceDerivativeKernel
open GppRegulatedBoxSpenceConstancy

/-- The elementary quotient needed to control the logarithmic cross term. -/
theorem log_one_sub_div_tendsto_neg_one :
    Tendsto (fun x : ℝ => Real.log (1 - x) / x)
      (𝓝[Ioo (0 : ℝ) 1] 0) (𝓝 (-1 : ℝ)) := by
  have hone_sub : HasDerivAt (fun y : ℝ => 1 - y) (-1) 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0) using 1 <;> ring
  have hlog1 : HasDerivAt Real.log 1 1 := by
    simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hlog1' : HasDerivAt Real.log 1 ((fun y : ℝ => 1 - y) 0) := by
    simpa using hlog1
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1) 0 := by
    simpa using hlog1'.comp 0 hone_sub
  have hright :
      𝓝[Ioo (0 : ℝ) 1] 0 ≤ 𝓝[>] (0 : ℝ) := by
    rw [nhdsWithin_le_iff]
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hy.1
  have hslope := hlog.tendsto_slope_zero_right.mono_left hright
  simpa [div_eq_mul_inv, mul_comm] using hslope

/-- The logarithmic cross term in Spence's formula vanishes at the left endpoint. -/
theorem log_mul_log_one_sub_tendsto_zero :
    Tendsto (fun x : ℝ => Real.log x * Real.log (1 - x))
      (𝓝[Ioo (0 : ℝ) 1] 0) (𝓝 0) := by
  have hcont : ContinuousAt (fun x : ℝ => x * Real.log x) 0 := by
    exact Real.continuous_mul_log.continuousAt
  have hmul :
      Tendsto (fun x : ℝ => x * Real.log x)
        (𝓝[Ioo (0 : ℝ) 1] 0) (𝓝 0) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hratio := log_one_sub_div_tendsto_neg_one
  have hraw :
      Tendsto
        (fun x : ℝ => (x * Real.log x) * (Real.log (1 - x) / x))
        (𝓝[Ioo (0 : ℝ) 1] 0) (𝓝 0) := by
    simpa using hmul.mul hratio
  have heq :
      (fun x : ℝ => (x * Real.log x) * (Real.log (1 - x) / x)) =ᶠ[
        𝓝[Ioo (0 : ℝ) 1] 0]
      (fun x : ℝ => Real.log x * Real.log (1 - x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxne : x ≠ 0 := ne_of_gt hx.1
    field_simp [hxne]
    ring
  exact (tendsto_congr' heq).mp hraw

/-- The stationary Spence combination has the Basel value on the whole open unit interval. -/
theorem spenceCombination_eq_pi_sq_div_six
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    spenceCombination x = Real.pi ^ 2 / 6 := by
  let L : Filter ℝ := 𝓝[Ioo (0 : ℝ) 1] 0
  have hL_le_zero : L ≤ 𝓝[Icc (0 : ℝ) 1] 0 := by
    dsimp [L]
    rw [nhdsWithin_le_iff]
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ⟨hy.1.le, hy.2.le⟩
  have hLx : Tendsto li2Series L (𝓝 0) :=
    li2Series_tendsto_zero_within.mono_left hL_le_zero
  have hmap :
      Tendsto (fun y : ℝ => 1 - y) L (𝓝[Icc (0 : ℝ) 1] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : ContinuousAt (fun y : ℝ => 1 - y) 0 := by fun_prop
      simpa [L] using hc.tendsto.mono_left (show L ≤ 𝓝 (0 : ℝ) by
        dsimp [L]
        exact nhdsWithin_le_nhds)
    · dsimp [L]
      filter_upwards [self_mem_nhdsWithin] with y hy
      rcases hy with ⟨hy0, hy1⟩
      constructor <;> linarith
  have hL1x :
      Tendsto (fun y : ℝ => li2Series (1 - y)) L (𝓝 (Real.pi ^ 2 / 6)) :=
    li2Series_tendsto_pi_sq_div_six.comp hmap
  have hlog :
      Tendsto (fun y : ℝ => Real.log y * Real.log (1 - y)) L (𝓝 0) := by
    simpa [L] using log_mul_log_one_sub_tendsto_zero
  have hlimit : Tendsto spenceCombination L (𝓝 (Real.pi ^ 2 / 6)) := by
    have H := (hLx.add hL1x).add hlog
    simpa [spenceCombination] using H
  have hx : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
  have hconst : Tendsto spenceCombination L (𝓝 (spenceCombination x)) := by
    have heq : spenceCombination =ᶠ[L] (fun _ : ℝ => spenceCombination x) := by
      dsimp [L]
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact spenceCombination_eq_on_Ioo hy hx
    exact (tendsto_congr' heq).mpr tendsto_const_nhds
  haveI : NeBot L := by
    dsimp [L]
    exact left_nhdsWithin_Ioo_neBot (by norm_num : (0 : ℝ) < 1)
  exact tendsto_nhds_unique hconst hlimit

/-- **Real Spence identity for the project's local dilogarithm series.** -/
theorem li2Series_spence
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    li2Series x + li2Series (1 - x) =
      Real.pi ^ 2 / 6 - Real.log x * Real.log (1 - x) := by
  have h := spenceCombination_eq_pi_sq_div_six hx0 hx1
  unfold spenceCombination at h
  linarith

end GppRegulatedBoxSpenceIdentity

#print axioms GppRegulatedBoxSpenceIdentity.log_one_sub_div_tendsto_neg_one
#print axioms GppRegulatedBoxSpenceIdentity.log_mul_log_one_sub_tendsto_zero
#print axioms GppRegulatedBoxSpenceIdentity.spenceCombination_eq_pi_sq_div_six
#print axioms GppRegulatedBoxSpenceIdentity.li2Series_spence
