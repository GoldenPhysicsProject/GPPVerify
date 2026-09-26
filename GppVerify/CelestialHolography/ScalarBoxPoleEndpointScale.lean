import GppVerify.CelestialHolography.ScalarBoxRegulatorBounds
import GppVerify.CelestialHolography.ScalarBoxEndpointLinearization
import GppVerify.CelestialHolography.ScalarBoxLogBounds
import Mathlib.Tactic

/-!
# Exact pole-endpoint regulator scale

The moving pole argument in the regulated scalar box is

`q / a - 1`.

The discovery calculation introduces `η = m/S`, `δ = 4m/U`, and a bounded positive
factor `B`. This file proves the exact identity `q/a - 1 = η B`; no asymptotic
replacement is made, and then derives explicit linear regulator bounds for the local
logarithm and dilogarithm corrections at that endpoint.
-/

namespace GppScalarBoxPoleEndpointScale

open GppScalarBoxRegulatorAlgebra
open GppScalarBoxEndpointLinearization
open GppScalarBoxRegulatorBounds
open GppScalarBoxLogBounds
open GppRegulatedBoxDilogSeries

/-- Exact identification of the pole endpoint with its natural regulator scale.

With `δ=4m/U`, `η=m/S`, and

`B = 2(1+κ)/[(1+δ)(1+κR)(1+R)(1-η)]`,

the Möbius endpoint obeys `q/a - 1 = η B`. -/
theorem q_div_a_sub_one_eq_eta_mul_B
    {S U m R κ q a δ η B : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    (hm : 0 < m) (hmS : m < S)
    (hκlo : 1 ≤ κ)
    (hq : q = (1 - R) / (1 + R))
    (ha : a = (κ - 1) / (κ + 1))
    (hprodSq : (κ * R) ^ 2 =
      1 - 4 * m ^ 2 / (S * (U + 4 * m)))
    (hκsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U))
    (hδ : δ = 4 * m / U)
    (hη : η = m / S)
    (hB : B = 2 * (1 + κ) /
      ((1 + δ) * (1 + κ * R) * (1 + R) * (1 - η))) :
    q / a - 1 = η * B := by
  have hSm : 0 < S - m := sub_pos.mpr hmS
  have hSU : 0 < S * U := mul_pos hS hU
  have hU4 : 0 < U + 4 * m := by linarith
  have hSU4 : 0 < S * (U + 4 * m) := mul_pos hS hU4
  have hκRplus : 1 + κ * R ≠ 0 := by
    intro hz
    have hκR : κ * R = -1 := by linarith
    rw [hκR] at hprodSq
    have hfrac : 0 < 4 * m ^ 2 / (S * (U + 4 * m)) := by
      exact div_pos (by positivity) hSU4
    nlinarith
  have hRplus : 1 + R ≠ 0 := by
    intro hz
    have hR : R = -1 := by linarith
    rw [hR] at hprodSq
    have hfrac : 0 < 4 * m ^ 2 / (S * (U + 4 * m)) := by
      exact div_pos (by positivity) hSU4
    have hκsqLower : 1 < κ ^ 2 := by
      rw [hκsq]
      have hnum : 0 < 4 * m * (S - m) := by positivity
      have hcorr : 0 < 4 * m * (S - m) / (S * U) := div_pos hnum hSU
      linarith
    nlinarith
  have hκplus : 1 + κ ≠ 0 := by linarith
  have hqa := q_sub_a_exact_m_sq S U m R κ q a
    hSU4.ne' hκRplus hRplus hκplus hq ha hprodSq
  have haExact := a_exact_linear_m
    hSU.ne' (by linarith : κ + 1 ≠ 0) ha hκsq
  have ha0 : a ≠ 0 := by
    rw [haExact]
    have hnum : 0 < 4 * m * (S - m) := by positivity
    have hden : 0 < S * U * (κ + 1) ^ 2 := by
      exact mul_pos hSU (sq_pos_of_pos (by linarith : 0 < κ + 1))
    exact (div_pos hnum hden).ne'
  rw [div_sub_one ha0, hqa, haExact, hB, hδ, hη]
  field_simp [hS.ne', hU.ne', hm.ne', sub_ne_zero.mpr hmS.ne']
  ring

/-- Once the exact pole-scale identity is known, the certified `B` interval immediately
places the physical pole argument inside the local dilogarithm disk. -/
theorem q_div_a_sub_one_small
    {q a η B : ℝ}
    (ht : q / a - 1 = η * B)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hB0 : 0 ≤ B) (hB : B ≤ 48 / 31) :
    0 ≤ q / a - 1 ∧
      q / a - 1 ≤ 12 / 31 ∧
      q / a - 1 < 1 / 2 := by
  rw [ht]
  exact eta_mul_B_small η B hη0 hη hB0 hB

/-- The pole-endpoint logarithmic correction is linear in `η=m/S`. -/
theorem abs_log_one_sub_etaB_le_linear_eta
    {η B : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hB0 : 0 ≤ B) (hB : B ≤ 48 / 31) :
    |Real.log (1 - η * B)| ≤ (72 / 31 : ℝ) * η := by
  rcases eta_mul_B_small η B hη0 hη hB0 hB with ⟨hx0, _, hxhalf⟩
  have hxB : η * B ≤ η * (48 / 31 : ℝ) :=
    mul_le_mul_of_nonneg_left hB hη0
  calc
    |Real.log (1 - η * B)| ≤ (3 / 2 : ℝ) * (η * B) :=
      abs_log_one_sub_le_three_halves hx0 hxhalf.le
    _ ≤ (3 / 2 : ℝ) * (η * (48 / 31 : ℝ)) :=
      mul_le_mul_of_nonneg_left hxB (by norm_num)
    _ = (72 / 31 : ℝ) * η := by ring

/-- The positive pole-endpoint dilogarithm correction is linear in `η=m/S`. -/
theorem abs_li2Series_etaB_le_linear_eta
    {η B : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hB0 : 0 ≤ B) (hB : B ≤ 48 / 31) :
    |li2Series (η * B)| ≤ (48 / 19 : ℝ) * η := by
  rcases eta_mul_B_small η B hη0 hη hB0 hB with ⟨hx0, hxupper, hxhalf⟩
  have hx1 : η * B < 1 := hxhalf.trans (by norm_num)
  have hden : 0 < 1 - η * B := by linarith
  have hxB : η * B ≤ (48 / 31 : ℝ) * η := by
    have := mul_le_mul_of_nonneg_left hB hη0
    nlinarith
  have hdenlower : (19 / 31 : ℝ) ≤ 1 - η * B := by linarith
  have hscaled : (48 / 31 : ℝ) * η ≤
      (48 / 19 : ℝ) * η * (1 - η * B) := by
    have hnon : 0 ≤ (48 / 19 : ℝ) * η := by positivity
    have hm := mul_le_mul_of_nonneg_left hdenlower hnon
    convert hm using 1 <;> ring
  have hfrac : η * B / (1 - η * B) ≤ (48 / 19 : ℝ) * η := by
    apply (div_le_iff₀ hden).2
    exact hxB.trans hscaled
  exact (abs_li2Series_le_of_nonneg hx0 hx1).trans hfrac

/-- The negative pole-endpoint dilogarithm correction obeys the same linear bound. -/
theorem abs_li2Series_neg_etaB_le_linear_eta
    {η B : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hB0 : 0 ≤ B) (hB : B ≤ 48 / 31) :
    |li2Series (-(η * B))| ≤ (48 / 19 : ℝ) * η := by
  rcases eta_mul_B_small η B hη0 hη hB0 hB with ⟨hx0, hxupper, hxhalf⟩
  have hx1 : η * B < 1 := hxhalf.trans (by norm_num)
  have hden : 0 < 1 - η * B := by linarith
  have hxB : η * B ≤ (48 / 31 : ℝ) * η := by
    have := mul_le_mul_of_nonneg_left hB hη0
    nlinarith
  have hdenlower : (19 / 31 : ℝ) ≤ 1 - η * B := by linarith
  have hscaled : (48 / 31 : ℝ) * η ≤
      (48 / 19 : ℝ) * η * (1 - η * B) := by
    have hnon : 0 ≤ (48 / 19 : ℝ) * η := by positivity
    have hm := mul_le_mul_of_nonneg_left hdenlower hnon
    convert hm using 1 <;> ring
  have hfrac : η * B / (1 - η * B) ≤ (48 / 19 : ℝ) * η := by
    apply (div_le_iff₀ hden).2
    exact hxB.trans hscaled
  exact (abs_li2Series_neg_le_of_nonneg hx0 hx1).trans hfrac

/-- The physical pole logarithm inherits the explicit `O(m/S)` bound after substituting
`t=q/a-1=ηB`. -/
theorem abs_log_one_sub_q_div_a_sub_one_le_linear_eta
    {q a η B : ℝ}
    (ht : q / a - 1 = η * B)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hB0 : 0 ≤ B) (hB : B ≤ 48 / 31) :
    |Real.log (1 - (q / a - 1))| ≤ (72 / 31 : ℝ) * η := by
  rw [ht]
  exact abs_log_one_sub_etaB_le_linear_eta hη0 hη hB0 hB

end GppScalarBoxPoleEndpointScale

#print axioms GppScalarBoxPoleEndpointScale.q_div_a_sub_one_eq_eta_mul_B
#print axioms GppScalarBoxPoleEndpointScale.q_div_a_sub_one_small
#print axioms GppScalarBoxPoleEndpointScale.abs_log_one_sub_etaB_le_linear_eta
#print axioms GppScalarBoxPoleEndpointScale.abs_li2Series_etaB_le_linear_eta
#print axioms GppScalarBoxPoleEndpointScale.abs_li2Series_neg_etaB_le_linear_eta
#print axioms GppScalarBoxPoleEndpointScale.abs_log_one_sub_q_div_a_sub_one_le_linear_eta
