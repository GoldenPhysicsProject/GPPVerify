import GppVerify.CelestialHolography.ScalarBoxRegulatorAlgebra
import GppVerify.CelestialHolography.RegulatedBoxDilogSeries
import Mathlib.Tactic

/-!
# Uniform scalar-box regulator bounds

This file promotes the explicit rational interval estimates derived in
`GPPDiscovery2/discovery/celestial_box/REGULATOR_UNIFORM_SCALE_BOUNDS.md`.
-/

namespace GppScalarBoxRegulatorBounds

open GppRegulatedBoxDilogSeries
open GppScalarBoxRegulatorAlgebra

/-- If `0 ≤ δ,η ≤ 1/4`, `κ ≥ 0`, and
`κ² = 1 + δ(1-η)`, then the rational bounds `1 ≤ κ ≤ 9/8` hold. -/
theorem kappa_mem_rational_interval
    (δ η κ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hκ0 : 0 ≤ κ)
    (hsq : κ ^ 2 = 1 + δ * (1 - η)) :
    1 ≤ κ ∧ κ ≤ 9 / 8 := by
  have h1η : 0 ≤ 1 - η := by linarith
  have hlowerSq : 1 ≤ κ ^ 2 := by
    rw [hsq]
    have := mul_nonneg hδ0 h1η
    linarith
  have hδη : 0 ≤ δ * η := mul_nonneg hδ0 hη0
  have hupperSq : κ ^ 2 ≤ 5 / 4 := by
    rw [hsq]
    nlinarith
  constructor <;> nlinarith

/-- If `0 ≤ δ ≤ 1/4`, `R ≥ 0`, and `R² = 1/(1+δ)`, then
`8/9 ≤ R ≤ 1`. -/
theorem R_mem_rational_interval
    (δ R : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hR0 : 0 ≤ R)
    (hsq : R ^ 2 = 1 / (1 + δ)) :
    8 / 9 ≤ R ∧ R ≤ 1 := by
  have hden : 0 < 1 + δ := by linarith
  have hupperSq : R ^ 2 ≤ 1 := by
    rw [hsq]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hlowerSq : (8 / 9 : ℝ) ^ 2 ≤ R ^ 2 := by
    rw [hsq]
    apply (le_div_iff₀ hden).2
    nlinarith
  constructor <;> nlinarith

/-- Under the exact product relation `(κR)² = 1 - δη/(1+δ)`,
`15/16 ≤ κR ≤ 1`. -/
theorem kappaR_mem_rational_interval
    (δ η x : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hx0 : 0 ≤ x)
    (hsq : x ^ 2 = 1 - δ * η / (1 + δ)) :
    15 / 16 ≤ x ∧ x ≤ 1 := by
  have hden : 0 < 1 + δ := by linarith
  have hδη0 : 0 ≤ δ * η := mul_nonneg hδ0 hη0
  have hδηle : δ * η ≤ 1 / 16 := by nlinarith
  have hfrac0 : 0 ≤ δ * η / (1 + δ) := div_nonneg hδη0 hden.le
  have hfracle : δ * η / (1 + δ) ≤ 1 / 16 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hupperSq : x ^ 2 ≤ 1 := by
    rw [hsq]
    linarith
  have hlowerSq : (15 / 16 : ℝ) ^ 2 ≤ x ^ 2 := by
    rw [hsq]
    nlinarith
  constructor <;> nlinarith

/-- `A = 4(1-η)/(1+κ)^2` lies in `[192/289,1]`. -/
theorem A_mem_rational_interval
    (η κ A : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hκlo : 1 ≤ κ) (hκhi : κ ≤ 9 / 8)
    (hA : A = 4 * (1 - η) / (1 + κ) ^ 2) :
    192 / 289 ≤ A ∧ A ≤ 1 := by
  have hbase : 0 < 1 + κ := by linarith
  have hden : 0 < (1 + κ) ^ 2 := sq_pos_of_pos hbase
  rw [hA]
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith [sq_nonneg (κ - 1), sq_nonneg (9 / 8 - κ)]
  · apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg (κ - 1)]

/-- If `0 ≤ r ≤ 1/8`, then `Q = 1/(1+r+r²/4)` lies in `[256/289,1]`. -/
theorem Q_mem_rational_interval
    (r Q : ℝ)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 8)
    (hQ : Q = 1 / (1 + r + r ^ 2 / 4)) :
    256 / 289 ≤ Q ∧ Q ≤ 1 := by
  have hden : 0 < 1 + r + r ^ 2 / 4 := by nlinarith [sq_nonneg r]
  have hrsq : r ^ 2 ≤ 1 / 64 := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr)]
  rw [hQ]
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith
  · apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg r]

/-- Pole-endpoint normalization bound. -/
theorem B_pos_and_le
    (δ η κ x R B : ℝ)
    (hδ0 : 0 ≤ δ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hκlo : 1 ≤ κ) (hκhi : κ ≤ 9 / 8)
    (hxlo : 15 / 16 ≤ x)
    (hRlo : 8 / 9 ≤ R)
    (hB : B = 2 * (1 + κ) /
      ((1 + δ) * (1 + x) * (1 + R) * (1 - η))) :
    0 < B ∧ B ≤ 48 / 31 := by
  have h1δ : 0 < 1 + δ := by linarith
  have h1x : 0 < 1 + x := by linarith
  have h1R : 0 < 1 + R := by linarith
  have h1η : 0 < 1 - η := by linarith
  have hden : 0 < (1 + δ) * (1 + x) * (1 + R) * (1 - η) := by positivity
  rw [hB]
  constructor
  · exact div_pos (by nlinarith) hden
  · apply (div_le_iff₀ hden).2
    have hnum : 2 * (1 + κ) ≤ (17 / 4 : ℝ) := by linarith
    have hδlo : (1 : ℝ) ≤ 1 + δ := by linarith
    have hxlo' : (31 / 16 : ℝ) ≤ 1 + x := by linarith
    have hRlo' : (17 / 9 : ℝ) ≤ 1 + R := by linarith
    have hηlo : (3 / 4 : ℝ) ≤ 1 - η := by linarith
    have hp1 : (1 : ℝ) * (31 / 16) ≤ (1 + δ) * (1 + x) := by
      exact mul_le_mul hδlo hxlo' (by norm_num) h1δ.le
    have hp1non : 0 ≤ (1 + δ) * (1 + x) := mul_nonneg h1δ.le h1x.le
    have hp2 : ((1 : ℝ) * (31 / 16)) * (17 / 9) ≤
        ((1 + δ) * (1 + x)) * (1 + R) := by
      exact mul_le_mul hp1 hRlo' (by norm_num) hp1non
    have hp2non : 0 ≤ ((1 + δ) * (1 + x)) * (1 + R) :=
      mul_nonneg hp1non h1R.le
    have hp3 : (((1 : ℝ) * (31 / 16)) * (17 / 9)) * (3 / 4) ≤
        (((1 + δ) * (1 + x)) * (1 + R)) * (1 - η) := by
      exact mul_le_mul hp2 hηlo (by norm_num) hp2non
    have hdenlower : (527 / 192 : ℝ) ≤
        (1 + δ) * (1 + x) * (1 + R) * (1 - η) := by
      norm_num at hp3 ⊢
      exact hp3
    nlinarith

/-- The exact Möbius endpoint separation is uniformly quadratic in the regulator.
Under the rational interval bounds already established for the physical domain,
`q-a` is nonnegative and is bounded by `(576/527) m²/(SU)`. -/
theorem q_sub_a_nonneg_and_le_m_sq
    {S U m R κ q a : ℝ}
    (hS : 0 < S) (hU : 0 < U) (hm : 0 ≤ m)
    (hκRlo : 15 / 16 ≤ κ * R)
    (hRlo : 8 / 9 ≤ R)
    (hκlo : 1 ≤ κ)
    (hq : q = (1 - R) / (1 + R))
    (ha : a = (κ - 1) / (κ + 1))
    (hsq : (κ * R) ^ 2 = 1 - 4 * m ^ 2 / (S * (U + 4 * m))) :
    0 ≤ q - a ∧
      q - a ≤ (576 / 527 : ℝ) * (m ^ 2 / (S * U)) := by
  have hU4 : 0 < U + 4 * m := by linarith
  have hSUpos : 0 < S * (U + 4 * m) := mul_pos hS hU4
  have hpluspos : 0 < 1 + κ * R := by linarith
  have hRpluspos : 0 < 1 + R := by linarith
  have hκpluspos : 0 < 1 + κ := by linarith
  have hfac := q_sub_a_exact_m_sq S U m R κ q a
    hSUpos.ne' hpluspos.ne' hRpluspos.ne' hκpluspos.ne' hq ha hsq
  rw [hfac]
  have hSUstep : S * U ≤ S * (U + 4 * m) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hS.le
  have h1κR : (31 / 16 : ℝ) ≤ 1 + κ * R := by linarith
  have h1R : (17 / 9 : ℝ) ≤ 1 + R := by linarith
  have h1κ : (2 : ℝ) ≤ 1 + κ := by linarith
  have hp1 : (S * U) * (31 / 16 : ℝ) ≤
      (S * (U + 4 * m)) * (1 + κ * R) := by
    exact mul_le_mul hSUstep h1κR (by norm_num) hSUpos.le
  have hp1non : 0 ≤ (S * (U + 4 * m)) * (1 + κ * R) := by positivity
  have hp2 : ((S * U) * (31 / 16 : ℝ)) * (17 / 9 : ℝ) ≤
      ((S * (U + 4 * m)) * (1 + κ * R)) * (1 + R) := by
    exact mul_le_mul hp1 h1R (by positivity) hp1non
  have hp2non :
      0 ≤ ((S * (U + 4 * m)) * (1 + κ * R)) * (1 + R) := by positivity
  have hp3 : (((S * U) * (31 / 16 : ℝ)) * (17 / 9 : ℝ)) * 2 ≤
      (((S * (U + 4 * m)) * (1 + κ * R)) * (1 + R)) * (1 + κ) := by
    exact mul_le_mul hp2 h1κ (by norm_num) hp2non
  have hdenlower : (527 / 72 : ℝ) * (S * U) ≤
      S * (U + 4 * m) * (1 + κ * R) * (1 + R) * (1 + κ) := by
    convert hp3 using 1 <;> ring
  have hbasepos : 0 < (527 / 72 : ℝ) * (S * U) := by positivity
  have hdenpos :
      0 < S * (U + 4 * m) * (1 + κ * R) * (1 + R) * (1 + κ) := by
    positivity
  have hnum0 : 0 ≤ 8 * m ^ 2 := by positivity
  constructor
  · exact div_nonneg hnum0 hdenpos.le
  · calc
      8 * m ^ 2 /
          (S * (U + 4 * m) * (1 + κ * R) * (1 + R) * (1 + κ)) ≤
          8 * m ^ 2 / ((527 / 72 : ℝ) * (S * U)) := by
            exact div_le_div_of_nonneg_left hnum0 hbasepos hdenlower
      _ = (576 / 527 : ℝ) * (m ^ 2 / (S * U)) := by
        field_simp [hS.ne', hU.ne']
        ring

/-- Absolute-value version of the quadratic endpoint-separation bound. -/
theorem abs_q_sub_a_le_m_sq
    {S U m R κ q a : ℝ}
    (hS : 0 < S) (hU : 0 < U) (hm : 0 ≤ m)
    (hκRlo : 15 / 16 ≤ κ * R)
    (hRlo : 8 / 9 ≤ R)
    (hκlo : 1 ≤ κ)
    (hq : q = (1 - R) / (1 + R))
    (ha : a = (κ - 1) / (κ + 1))
    (hsq : (κ * R) ^ 2 = 1 - 4 * m ^ 2 / (S * (U + 4 * m))) :
    |q - a| ≤ (576 / 527 : ℝ) * (m ^ 2 / (S * U)) := by
  rcases q_sub_a_nonneg_and_le_m_sq hS hU hm hκRlo hRlo hκlo hq ha hsq with
    ⟨hqa0, hqa⟩
  simpa [abs_of_nonneg hqa0] using hqa

/-- The dilogarithm endpoint `η B` is uniformly inside the elementary `x<1/2`
regime: `0 ≤ ηB ≤ 12/31 < 1/2`. -/
theorem eta_mul_B_small
    (η B : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hB0 : 0 ≤ B) (hB : B ≤ 48 / 31) :
    0 ≤ η * B ∧ η * B ≤ 12 / 31 ∧ η * B < 1 / 2 := by
  have hprod0 : 0 ≤ η * B := mul_nonneg hη0 hB0
  have hprod : η * B ≤ 12 / 31 := by
    calc
      η * B ≤ (1 / 4 : ℝ) * B := mul_le_mul_of_nonneg_right hη hB0
      _ ≤ (1 / 4 : ℝ) * (48 / 31 : ℝ) :=
        mul_le_mul_of_nonneg_left hB (by norm_num)
      _ = 12 / 31 := by norm_num
  constructor
  · exact hprod0
  · constructor
    · exact hprod
    · linarith

/-- Branch-free local dilogarithm control at the moving endpoint.  Combining
`η B ≤ 12/31` with the geometric-series majorant gives the exact uniform
constant `12/19` for both signs of the small argument. -/
theorem etaB_li2_uniform_bound
    (η B : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hB0 : 0 ≤ B) (hB : B ≤ 48 / 31) :
    |li2Series (η * B)| ≤ 12 / 19 ∧
    |li2Series (-(η * B))| ≤ 12 / 19 := by
  rcases eta_mul_B_small η B hη0 hη hB0 hB with ⟨hx0, hxupper, hxhalf⟩
  have hx1 : η * B < 1 := by linarith
  have hden : 0 < 1 - η * B := by linarith
  have hfrac : η * B / (1 - η * B) ≤ (12 : ℝ) / 19 := by
    apply (div_le_iff₀ hden).2
    linarith [hxupper]
  constructor
  · exact (abs_li2Series_le_of_nonneg hx0 hx1).trans hfrac
  · exact (abs_li2Series_neg_le_of_nonneg hx0 hx1).trans hfrac

end GppScalarBoxRegulatorBounds

#print axioms GppScalarBoxRegulatorBounds.kappa_mem_rational_interval
#print axioms GppScalarBoxRegulatorBounds.R_mem_rational_interval
#print axioms GppScalarBoxRegulatorBounds.kappaR_mem_rational_interval
#print axioms GppScalarBoxRegulatorBounds.A_mem_rational_interval
#print axioms GppScalarBoxRegulatorBounds.Q_mem_rational_interval
#print axioms GppScalarBoxRegulatorBounds.B_pos_and_le
#print axioms GppScalarBoxRegulatorBounds.q_sub_a_nonneg_and_le_m_sq
#print axioms GppScalarBoxRegulatorBounds.abs_q_sub_a_le_m_sq
#print axioms GppScalarBoxRegulatorBounds.eta_mul_B_small
#print axioms GppScalarBoxRegulatorBounds.etaB_li2_uniform_bound
