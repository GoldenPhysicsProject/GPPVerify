import GppVerify.CelestialHolography.ScalarBoxEndpointLinearization
import GppVerify.CelestialHolography.ScalarBoxLogBounds
import GppVerify.CelestialHolography.RegulatedBoxDilogSeries
import Mathlib.Tactic

/-!
# Quadratic product-endpoint bounds for the scalar-box regulator

The individual Möbius endpoints are linearly small in the regulator. Their product
therefore carries two powers of `m`. This file packages that observation with the local
logarithm and dilogarithm estimates used in the explicit scalar-box remainder.
-/

namespace GppScalarBoxProductEndpointBounds

open GppScalarBoxEndpointLinearization
open GppScalarBoxLogBounds
open GppRegulatedBoxDilogSeries

/-- The product of the two moving endpoints is quadratically small. -/
theorem aq_nonneg_and_le_quadratic_m
    {S U m R κ q a : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    (hm0 : 0 ≤ m) (hmS : m ≤ S)
    (hRlo : 8 / 9 ≤ R) (hκlo : 1 ≤ κ)
    (hq : q = (1 - R) / (1 + R))
    (ha : a = (κ - 1) / (κ + 1))
    (hRsq : R ^ 2 = U / (U + 4 * m))
    (hκsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U)) :
    0 ≤ a * q ∧
      a * q ≤ (324 / 289 : ℝ) * (m / U) ^ 2 := by
  rcases q_nonneg_and_le_linear_m hU hm0 hRlo hq hRsq with ⟨hq0, hqle⟩
  rcases a_nonneg_and_le_linear_m hS hU hm0 hmS hκlo ha hκsq with ⟨ha0, hale⟩
  have hscale0 : 0 ≤ m / U := div_nonneg hm0 hU.le
  constructor
  · exact mul_nonneg ha0 hq0
  · calc
      a * q ≤ (m / U) * q := mul_le_mul_of_nonneg_right hale hq0
      _ ≤ (m / U) * ((324 / 289 : ℝ) * (m / U)) :=
        mul_le_mul_of_nonneg_left hqle hscale0
      _ = (324 / 289 : ℝ) * (m / U) ^ 2 := by ring

/-- On the standard small-regulator interval, the product endpoint lies inside the
`1/2` disk needed by the elementary log/dilog estimates. -/
theorem aq_le_half
    {S U m R κ q a : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    (hm0 : 0 ≤ m) (hmS : m ≤ S) (hmU : m ≤ U / 16)
    (hRlo : 8 / 9 ≤ R) (hκlo : 1 ≤ κ)
    (hq : q = (1 - R) / (1 + R))
    (ha : a = (κ - 1) / (κ + 1))
    (hRsq : R ^ 2 = U / (U + 4 * m))
    (hκsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U)) :
    a * q ≤ (1 / 2 : ℝ) := by
  rcases aq_nonneg_and_le_quadratic_m hS hU hm0 hmS hRlo hκlo hq ha hRsq hκsq with
    ⟨_, hzle⟩
  have hx0 : 0 ≤ m / U := div_nonneg hm0 hU.le
  have hxle : m / U ≤ (1 / 16 : ℝ) := by
    apply (div_le_iff₀ hU).2
    nlinarith
  have hprod : 0 ≤ (m / U) * ((1 / 16 : ℝ) - m / U) :=
    mul_nonneg hx0 (by linarith)
  have hx2 : (m / U) ^ 2 ≤ (1 / 256 : ℝ) := by
    nlinarith
  nlinarith

/-- The logarithmic product-endpoint correction is explicitly quadratic in `m/U`. -/
theorem abs_log_one_sub_aq_le_quadratic_m
    {S U m R κ q a : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    (hm0 : 0 ≤ m) (hmS : m ≤ S) (hmU : m ≤ U / 16)
    (hRlo : 8 / 9 ≤ R) (hκlo : 1 ≤ κ)
    (hq : q = (1 - R) / (1 + R))
    (ha : a = (κ - 1) / (κ + 1))
    (hRsq : R ^ 2 = U / (U + 4 * m))
    (hκsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U)) :
    |Real.log (1 - a * q)| ≤
      (486 / 289 : ℝ) * (m / U) ^ 2 := by
  rcases aq_nonneg_and_le_quadratic_m hS hU hm0 hmS hRlo hκlo hq ha hRsq hκsq with
    ⟨hz0, hzle⟩
  have hzhalf := aq_le_half hS hU hm0 hmS hmU hRlo hκlo hq ha hRsq hκsq
  calc
    |Real.log (1 - a * q)| ≤ (3 / 2 : ℝ) * (a * q) :=
      abs_log_one_sub_le_three_halves hz0 hzhalf
    _ ≤ (3 / 2 : ℝ) * ((324 / 289 : ℝ) * (m / U) ^ 2) :=
      mul_le_mul_of_nonneg_left hzle (by norm_num)
    _ = (486 / 289 : ℝ) * (m / U) ^ 2 := by ring

/-- The positive product-endpoint dilogarithm correction is explicitly quadratic. -/
theorem abs_li2Series_aq_le_quadratic_m
    {S U m R κ q a : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    (hm0 : 0 ≤ m) (hmS : m ≤ S) (hmU : m ≤ U / 16)
    (hRlo : 8 / 9 ≤ R) (hκlo : 1 ≤ κ)
    (hq : q = (1 - R) / (1 + R))
    (ha : a = (κ - 1) / (κ + 1))
    (hRsq : R ^ 2 = U / (U + 4 * m))
    (hκsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U)) :
    |li2Series (a * q)| ≤
      (648 / 289 : ℝ) * (m / U) ^ 2 := by
  rcases aq_nonneg_and_le_quadratic_m hS hU hm0 hmS hRlo hκlo hq ha hRsq hκsq with
    ⟨hz0, hzle⟩
  have hzhalf := aq_le_half hS hU hm0 hmS hmU hRlo hκlo hq ha hRsq hκsq
  have hzlt1 : a * q < (1 : ℝ) := lt_of_le_of_lt hzhalf (by norm_num)
  have hli := abs_li2Series_le_of_nonneg hz0 hzlt1
  have hden : 0 < 1 - a * q := by linarith
  have hratio : (a * q) / (1 - a * q) ≤ 2 * (a * q) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  calc
    |li2Series (a * q)| ≤ (a * q) / (1 - a * q) := hli
    _ ≤ 2 * (a * q) := hratio
    _ ≤ 2 * ((324 / 289 : ℝ) * (m / U) ^ 2) :=
      mul_le_mul_of_nonneg_left hzle (by norm_num)
    _ = (648 / 289 : ℝ) * (m / U) ^ 2 := by ring

end GppScalarBoxProductEndpointBounds

#print axioms GppScalarBoxProductEndpointBounds.aq_nonneg_and_le_quadratic_m
#print axioms GppScalarBoxProductEndpointBounds.aq_le_half
#print axioms GppScalarBoxProductEndpointBounds.abs_log_one_sub_aq_le_quadratic_m
#print axioms GppScalarBoxProductEndpointBounds.abs_li2Series_aq_le_quadratic_m
