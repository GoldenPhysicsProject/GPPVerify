import GppVerify.CelestialHolography.RegulatedBoxDilogSignedZeroContinuity
import GppVerify.CelestialHolography.RegulatedBoxLandenConstancy
import Mathlib.Tactic

/-!
# Branch-free real Landen identity

The preceding derivative theorem shows that

  Li2(x/(1+x)) + Li2(-x) + (1/2) log(1+x)^2

is constant on `(0,1)`.  Both dilogarithm arguments tend to zero as `x -> 0+`,
and the logarithmic term tends to zero as well.  Signed endpoint continuity of the
real Li2 series therefore fixes the constant to zero without any complex branches.
-/

namespace GppRegulatedBoxLandenIdentity

open Set Filter
open scoped Topology
open GppRegulatedBoxDilogSeries
open GppRegulatedBoxDilogSignedZeroContinuity
open GppRegulatedBoxLandenDerivative
open GppRegulatedBoxLandenConstancy

/-- The stationary Landen combination has value zero on the open unit interval. -/
theorem landenCombination_eq_zero
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    landenCombination x = 0 := by
  let L : Filter ℝ := 𝓝[Ioo (0 : ℝ) 1] 0

  have hfrac : Tendsto (fun y : ℝ => y / (1 + y)) L
      (𝓝[Icc (-1 : ℝ) 1] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hnum : HasDerivAt (fun y : ℝ => y) 1 0 := hasDerivAt_id 0
      have hden : HasDerivAt (fun y : ℝ => 1 + y) 1 0 := by
        convert (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add (hasDerivAt_id 0) using 1 <;>
          norm_num
      have hc : ContinuousAt (fun y : ℝ => y / (1 + y)) 0 :=
        (hnum.div hden (by norm_num)).continuousAt
      simpa [L] using hc.tendsto.mono_left (show L ≤ 𝓝 (0 : ℝ) by
        dsimp [L]
        exact nhdsWithin_le_nhds)
    · dsimp [L]
      filter_upwards [self_mem_nhdsWithin] with y hy
      rcases hy with ⟨hy0, hy1⟩
      have hdenpos : 0 < 1 + y := by linarith
      have hyfrac0 : 0 ≤ y / (1 + y) := div_nonneg hy0.le hdenpos.le
      have hyfrac1 : y / (1 + y) ≤ 1 := by
        exact (div_le_one hdenpos).2 (by linarith)
      exact ⟨by linarith, hyfrac1⟩

  have hneg : Tendsto (fun y : ℝ => -y) L
      (𝓝[Icc (-1 : ℝ) 1] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : ContinuousAt (fun y : ℝ => -y) 0 := by fun_prop
      simpa [L] using hc.tendsto.mono_left (show L ≤ 𝓝 (0 : ℝ) by
        dsimp [L]
        exact nhdsWithin_le_nhds)
    · dsimp [L]
      filter_upwards [self_mem_nhdsWithin] with y hy
      rcases hy with ⟨hy0, hy1⟩
      exact ⟨by linarith, by linarith⟩

  have hLiFrac : Tendsto (fun y : ℝ => li2Series (y / (1 + y))) L (𝓝 0) :=
    li2Series_tendsto_zero_signed.comp hfrac
  have hLiNeg : Tendsto (fun y : ℝ => li2Series (-y)) L (𝓝 0) :=
    li2Series_tendsto_zero_signed.comp hneg

  have hlog : Tendsto (fun y : ℝ => (Real.log (1 + y)) ^ 2 / 2) L (𝓝 0) := by
    have hinner : HasDerivAt (fun y : ℝ => 1 + y) 1 0 := by
      convert (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add (hasDerivAt_id 0) using 1 <;>
        norm_num
    have hlogAtInner :
        HasDerivAt Real.log ((1 + (0 : ℝ))⁻¹) (1 + (0 : ℝ)) := by
      exact Real.hasDerivAt_log (by norm_num : (1 + (0 : ℝ)) ≠ 0)
    have hlogderiv : HasDerivAt (fun y : ℝ => Real.log (1 + y)) 1 0 := by
      have H := hlogAtInner.comp 0 hinner
      norm_num at H
      exact H
    have hc : ContinuousAt (fun y : ℝ => (Real.log (1 + y)) ^ 2 / 2) 0 := by
      exact (hlogderiv.pow 2).div_const 2 |>.continuousAt
    simpa using hc.tendsto.mono_left (show L ≤ 𝓝 (0 : ℝ) by
      dsimp [L]
      exact nhdsWithin_le_nhds)

  have hlimit : Tendsto landenCombination L (𝓝 0) := by
    have H := (hLiFrac.add hLiNeg).add hlog
    simpa [landenCombination] using H

  have hx : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
  have hconst : Tendsto landenCombination L (𝓝 (landenCombination x)) := by
    have heq : landenCombination =ᶠ[L] (fun _ : ℝ => landenCombination x) := by
      dsimp [L]
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact landenCombination_eq_on_Ioo hy hx
    exact (tendsto_congr' heq).mpr tendsto_const_nhds

  haveI : NeBot L := by
    dsimp [L]
    exact left_nhdsWithin_Ioo_neBot (by norm_num : (0 : ℝ) < 1)
  exact tendsto_nhds_unique hconst hlimit

/-- **Real Landen identity for the project's local dilogarithm series.** -/
theorem li2Series_landen
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    li2Series (x / (1 + x)) + li2Series (-x) =
      -(Real.log (1 + x)) ^ 2 / 2 := by
  have h := landenCombination_eq_zero hx0 hx1
  unfold landenCombination at h
  linarith

end GppRegulatedBoxLandenIdentity

#print axioms GppRegulatedBoxLandenIdentity.landenCombination_eq_zero
#print axioms GppRegulatedBoxLandenIdentity.li2Series_landen
