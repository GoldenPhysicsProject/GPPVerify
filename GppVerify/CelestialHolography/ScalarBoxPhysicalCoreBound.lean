import GppVerify.CelestialHolography.ScalarBoxStructuredPhysicalMajorant
import GppVerify.CelestialHolography.ScalarBoxLogScaleBounds
import GppVerify.CelestialHolography.ScalarBoxPoleLogScaleBounds
import GppVerify.CelestialHolography.ScalarBoxPhysicalSpecialRemainder
import Mathlib.Tactic

/-!
# Physical scalar-box core bound

This file discharges the three interfaces of the correct mixed-logarithm core estimate:
the lower-endpoint logarithmic replacement, the pole-endpoint logarithmic replacement,
and the six-term special-function remainder.
-/

namespace GppScalarBoxPhysicalCoreBound

open GppScalarBoxStructuredPhysicalMajorant
open GppScalarBoxLogSquareRemainder
open GppScalarBoxLogScaleBounds
open GppScalarBoxPoleLogScaleBounds
open GppScalarBoxRegulatorBounds
open GppScalarBoxPhysicalSpecialRemainder
open GppScalarBoxSpecialFunctionRemainder

/-- On the standard physical small-regulator chamber, the transformed regulated core
is bounded by the correct five-term structured majorant. -/
theorem abs_physical_structured_core_sub_D0_le
    {S U m R κ q a t ρ η B x δ : ℝ}
    (hS : 0 < S) (hU : 0 < U) (hm : 0 < m)
    (hmS : m ≤ S / 4) (hmU : m ≤ U / 16)
    (hRlo : 8 / 9 ≤ R) (hRhi : R ≤ 1)
    (hκlo : 1 ≤ κ) (hκhi : κ ≤ 9 / 8)
    (hxlo : 15 / 16 ≤ x) (hxhi : x ≤ 1)
    (hq : q = (1 - R) / (1 + R))
    (ha : a = (κ - 1) / (κ + 1))
    (hRsq : R ^ 2 = U / (U + 4 * m))
    (hκsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U))
    (hρ : ρ = m / U) (hη : η = m / S) (hδ : δ = 4 * m / U)
    (ht : t = η * B)
    (hBdef : B = 2 * (1 + κ) /
      ((1 + δ) * (1 + x) * (1 + R) * (1 - η)))
    (hκsqScale : κ ^ 2 = 1 + δ * (1 - η))
    (hxsq : x ^ 2 = 1 - δ * η / (1 + δ))
    (hRsqScale : R ^ 2 = 1 / (1 + δ)) :
    |structuredScalarBoxCore a t (specialRemainder a q t) -
      GppScalarBoxD0PrefactorVanishing.scalarBoxD0 S U m| ≤
      structuredPhysicalCoreMajorant S U m := by
  have hmS' : m ≤ S := by linarith
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδsmall : δ ≤ 1 / 4 := by
    rw [hδ]
    apply (div_le_iff₀ hU).2
    nlinarith
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have hηsmall : η ≤ 1 / 4 := by
    rw [hη]
    apply (div_le_iff₀ hS).2
    nlinarith
  have hBpair := B_pos_and_le δ η κ x R B
    hδ0 hη0 hηsmall hκlo hκhi hxlo hRlo hBdef
  have haLog := abs_log_a_sub_log_m_div_U_le
    hS hU hm hmS' hδ0 hδsmall hη0 hηsmall hκlo hκhi
    ha hκsq hη hκsqScale
  have haLog' : |Real.log a - Real.log (m / U)| ≤
      lowerLogError (4 * m / U) (m / S) := by
    rw [GppScalarBoxRegulatorVanishing.lowerLogError_regulator_polynomial hS.ne' hU.ne']
    rw [hδ, hη] at haLog
    convert haLog using 1 <;> ring
  have htLog := abs_log_t_sub_log_m_div_S_le
    hS hm hδ0 hδsmall hη0 hηsmall hκlo hκhi
    hxlo hxhi hRlo hRhi hκsqScale hxsq hRsqScale hBdef hη ht
  have htLog' : |Real.log t - Real.log (m / S)| ≤
      poleLogError (4 * m / U) (m / S) := by
    rw [GppScalarBoxRegulatorVanishing.poleLogError_regulator_polynomial hS.ne' hU.ne']
    rw [hδ, hη] at htLog
    convert htLog using 1 <;> ring
  have hE := abs_specialRemainder_le_physical
    hS hU hm hmS hmU hRlo hRhi hκlo hq ha hRsq hκsq hρ hη ht
    hBpair.1.le hBpair.2
  have hE' : |specialRemainder a q t| ≤
      specialRemainderMajorant (m / U) (m / S) := by
    simpa [hρ, hη] using hE
  exact abs_structuredScalarBoxCore_sub_D0_le hS hU hm haLog' htLog' hE'

end GppScalarBoxPhysicalCoreBound

#print axioms GppScalarBoxPhysicalCoreBound.abs_physical_structured_core_sub_D0_le
