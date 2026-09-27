import GppVerify.CelestialHolography.ScalarBoxSpecialFunctionRemainder
import GppVerify.CelestialHolography.ScalarBoxQLogScale
import GppVerify.CelestialHolography.ScalarBoxProductEndpointBounds
import GppVerify.CelestialHolography.ScalarBoxPoleEndpointScale
import GppVerify.CelestialHolography.ScalarBoxLogBounds
import GppVerify.CelestialHolography.ScalarBoxEndpointLinearization
import Mathlib.Tactic

/-!
# Physical assembly of the scalar-box special-function remainder

This file discharges the abstract component hypotheses of
`GppScalarBoxSpecialFunctionRemainder.abs_specialRemainder_le` from the certified
physical endpoint estimates.  The only pole input retained as an interface is the exact
already-derived scale identity `t = eta * B` together with the certified interval
`0 <= B <= 48/31`.
-/

namespace GppScalarBoxPhysicalSpecialRemainder

open GppRegulatedBoxDilogSeries
open GppScalarBoxSpecialFunctionRemainder
open GppScalarBoxQLogScale
open GppScalarBoxProductEndpointBounds
open GppScalarBoxPoleEndpointScale
open GppScalarBoxLogBounds
open GppScalarBoxEndpointLinearization

/-- On the standard physical small-regulator chamber, the complete six-term special
remainder is bounded by the explicit dimensionless majorant `E_*`. -/
theorem abs_specialRemainder_le_physical
    {S U m R κ q a t ρ η B : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    (hm : 0 < m)
    (hmS : m ≤ S / 4) (hmU : m ≤ U / 16)
    (hRlo : 8 / 9 ≤ R) (hRhi : R ≤ 1)
    (hκlo : 1 ≤ κ)
    (hq : q = (1 - R) / (1 + R))
    (ha : a = (κ - 1) / (κ + 1))
    (hRsq : R ^ 2 = U / (U + 4 * m))
    (hκsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U))
    (hρ : ρ = m / U) (hη : η = m / S)
    (ht : t = η * B)
    (hB0 : 0 ≤ B) (hB : B ≤ 48 / 31) :
    |specialRemainder a q t| ≤ specialRemainderMajorant ρ η := by
  have hm0 : 0 ≤ m := hm.le
  have hmS' : m ≤ S := by linarith
  have hmUhalf : m ≤ U / 2 := by linarith
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρsmall : ρ ≤ 1 / 16 := by
    rw [hρ]
    exact (div_le_iff₀ hU).2 (by nlinarith)
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have hηsmall : η ≤ 1 / 4 := by
    rw [hη]
    exact (div_le_iff₀ hS).2 (by nlinarith)

  have hat : |li2Series (-t)| ≤ (48 / 19 : ℝ) * η := by
    rw [ht]
    exact abs_li2Series_neg_etaB_le_linear_eta hη0 hηsmall hB0 hB

  have haqLi : |li2Series (a * q)| ≤ (648 / 289 : ℝ) * ρ ^ 2 := by
    have h := abs_li2Series_aq_le_quadratic_m
      hS hU hm0 hmS' hmU hRlo hκlo hq ha hRsq hκsq
    simpa [hρ] using h

  have hqlog : |Real.log q| ≤ |Real.log ρ| + (81 / 32 : ℝ) * ρ := by
    exact abs_log_q_le_abs_log_rho_add
      hU hm hmU hRlo hRhi hq hRsq hρ

  have haqLog : |Real.log (1 - a * q)| ≤ (486 / 289 : ℝ) * ρ ^ 2 := by
    have h := abs_log_one_sub_aq_le_quadratic_m
      hS hU hm0 hmS' hmU hRlo hκlo hq ha hRsq hκsq
    simpa [hρ] using h

  have haLog :
      (1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2 ≤ (9 / 8 : ℝ) * ρ ^ 2 := by
    have h := half_log_one_sub_a_sq_le_linear_m_sq
      hS hU hm0 hmS' hmUhalf hκlo ha hκsq
    simpa [hρ] using h

  rcases a_nonneg_and_le_linear_m hS hU hm0 hmS' hκlo ha hκsq with
    ⟨ha0, hale⟩
  have haρ : a ≤ ρ := by simpa [hρ] using hale
  have haNeg : |li2Series (-(a / (1 - a)))| ≤ (8 / 7 : ℝ) * ρ :=
    abs_li2Series_neg_a_div_one_sub_a_le_rho hρ0 hρsmall ha0 haρ
  have haPos : |li2Series a| ≤ (16 / 15 : ℝ) * ρ :=
    abs_li2Series_a_le_rho hρ0 hρsmall ha0 haρ

  exact abs_specialRemainder_le hρ0 hη0 hat haqLi hqlog haqLog haLog haNeg haPos

end GppScalarBoxPhysicalSpecialRemainder

#print axioms GppScalarBoxPhysicalSpecialRemainder.abs_specialRemainder_le_physical
