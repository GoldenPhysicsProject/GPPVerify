import GppVerify.CelestialHolography.RegulatedBoxDilogNegativeEndpointContinuity
import GppVerify.CelestialHolography.RegulatedBoxLandenIdentity
import GppVerify.CelestialHolography.RegulatedBoxSpenceIdentity
import Mathlib.Tactic

/-!
# The negative unit endpoint value of the real dilogarithm series

Take the branch-free Landen identity to `x -> 1-` to obtain

  Li2(1/2) + Li2(-1) + (1/2) log(2)^2 = 0.

Spence at `x = 1/2` gives

  2 Li2(1/2) = pi^2/6 - log(2)^2.

Eliminating `Li2(1/2)` yields `Li2(-1) = -pi^2/12`, entirely within the real
power-series model and without an independent alternating-Basel theorem.
-/

namespace GppRegulatedBoxDilogNegativeOneValue

open Set Filter
open scoped Topology
open GppRegulatedBoxDilogSeries
open GppRegulatedBoxDilogDerivative
open GppRegulatedBoxDilogNegativeEndpointContinuity
open GppRegulatedBoxLandenDerivative
open GppRegulatedBoxLandenIdentity
open GppRegulatedBoxSpenceIdentity

/-- Endpoint form of the Landen identity at `x = 1`. -/
theorem landen_at_one_endpoint :
    li2Series (1 / 2 : ℝ) + li2Series (-1) + (Real.log 2) ^ 2 / 2 = 0 := by
  let L : Filter ℝ := 𝓝[Ioo (0 : ℝ) 1] 1

  have hfrac : Tendsto (fun y : ℝ => y / (1 + y)) L (𝓝 (1 / 2 : ℝ)) := by
    have hnum : HasDerivAt (fun y : ℝ => y) 1 1 := hasDerivAt_id 1
    have hden : HasDerivAt (fun y : ℝ => 1 + y) 1 1 := by
      convert (hasDerivAt_const (x := (1 : ℝ)) (c := (1 : ℝ))).add (hasDerivAt_id 1) using 1 <;>
        norm_num
    have hc : ContinuousAt (fun y : ℝ => y / (1 + y)) 1 :=
      (hnum.div hden (by norm_num)).continuousAt
    change Tendsto (fun y : ℝ => y / (1 + y)) (𝓝[Ioo (0 : ℝ) 1] 1) (𝓝 (1 / 2 : ℝ))
    convert hc.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[Ioo (0 : ℝ) 1] 1 ≤ 𝓝 1) using 1 <;> norm_num

  have hhalf_cont : ContinuousAt li2Series (1 / 2 : ℝ) := by
    exact (hasDerivAt_li2Series (by norm_num) (by norm_num)).continuousAt
  have hLiFrac :
      Tendsto (fun y : ℝ => li2Series (y / (1 + y))) L
        (𝓝 (li2Series (1 / 2 : ℝ))) :=
    hhalf_cont.tendsto.comp hfrac

  have hneg : Tendsto (fun y : ℝ => -y) L
      (𝓝[Icc (-1 : ℝ) 1] (-1)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : ContinuousAt (fun y : ℝ => -y) 1 := by fun_prop
      simpa [L] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · dsimp [L]
      filter_upwards [self_mem_nhdsWithin] with y hy
      rcases hy with ⟨hy0, hy1⟩
      exact ⟨by linarith, by linarith⟩
  have hLiNeg :
      Tendsto (fun y : ℝ => li2Series (-y)) L (𝓝 (li2Series (-1))) :=
    li2Series_tendsto_neg_one_within.comp hneg

  have hlog :
      Tendsto (fun y : ℝ => (Real.log (1 + y)) ^ 2 / 2) L
        (𝓝 ((Real.log 2) ^ 2 / 2)) := by
    have hinner : HasDerivAt (fun y : ℝ => 1 + y) 1 1 := by
      convert (hasDerivAt_const (x := (1 : ℝ)) (c := (1 : ℝ))).add (hasDerivAt_id 1) using 1 <;>
        norm_num
    have hlogAt : HasDerivAt Real.log ((1 + 1 : ℝ)⁻¹) (1 + 1 : ℝ) := by
      convert Real.hasDerivAt_log (by norm_num : (2 : ℝ) ≠ 0) using 1 <;> norm_num
    have hlogderiv : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / 2) 1 := by
      convert hlogAt.comp 1 hinner using 1 <;> norm_num
    have hc : ContinuousAt (fun y : ℝ => (Real.log (1 + y)) ^ 2 / 2) 1 :=
      ((hlogderiv.pow 2).div_const 2).continuousAt
    change Tendsto (fun y : ℝ => (Real.log (1 + y)) ^ 2 / 2)
      (𝓝[Ioo (0 : ℝ) 1] 1) (𝓝 ((Real.log 2) ^ 2 / 2))
    convert hc.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[Ioo (0 : ℝ) 1] 1 ≤ 𝓝 1) using 1 <;> norm_num

  have hlimit :
      Tendsto landenCombination L
        (𝓝 (li2Series (1 / 2 : ℝ) + li2Series (-1) + (Real.log 2) ^ 2 / 2)) := by
    have H := (hLiFrac.add hLiNeg).add hlog
    simpa [landenCombination] using H

  have hzero : Tendsto landenCombination L (𝓝 0) := by
    have heq : landenCombination =ᶠ[L] (fun _ : ℝ => 0) := by
      dsimp [L]
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact landenCombination_eq_zero hy.1 hy.2
    exact (tendsto_congr' heq).mpr tendsto_const_nhds

  haveI : NeBot L := by
    dsimp [L]
    exact right_nhdsWithin_Ioo_neBot (by norm_num : (0 : ℝ) < 1)
  exact tendsto_nhds_unique hlimit hzero

/-- Spence at one half, with the logarithm written as `log 2`. -/
theorem two_mul_li2Series_half :
    2 * li2Series (1 / 2 : ℝ) = Real.pi ^ 2 / 6 - (Real.log 2) ^ 2 := by
  have hs := li2Series_spence (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hhalfsub : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hhalfsub] at hs
  have hhalfne : (1 / 2 : ℝ) ≠ 0 := by norm_num
  have htwone : (2 : ℝ) ≠ 0 := by norm_num
  have hlogmul := Real.log_mul hhalfne htwone
  have hmul : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  rw [hmul, Real.log_one] at hlogmul
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    linarith
  rw [hloghalf] at hs
  nlinarith

/-- **Exact negative unit endpoint value.** -/
theorem li2Series_neg_one :
    li2Series (-1) = -(Real.pi ^ 2) / 12 := by
  have hL := landen_at_one_endpoint
  have hS := two_mul_li2Series_half
  linarith

end GppRegulatedBoxDilogNegativeOneValue

#print axioms GppRegulatedBoxDilogNegativeOneValue.landen_at_one_endpoint
#print axioms GppRegulatedBoxDilogNegativeOneValue.two_mul_li2Series_half
#print axioms GppRegulatedBoxDilogNegativeOneValue.li2Series_neg_one
