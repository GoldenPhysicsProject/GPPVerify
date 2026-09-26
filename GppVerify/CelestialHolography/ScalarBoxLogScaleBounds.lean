import GppVerify.CelestialHolography.ScalarBoxEndpointLinearization
import GppVerify.CelestialHolography.ScalarBoxRegulatorBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Multiplicative logarithmic scale for the scalar-box lower endpoint

The exact lower Möbius endpoint factors as

  a = (m/U) A,
  A = 4(1-η)/(1+κ)^2,
  η = m/S.

On the physical small-regulator chamber, `A` lies in `[192/289,1]`.  This file
quantifies `1-A` and converts the multiplicative error into a logarithmic error using
Mathlib's elementary inequality `log x ≤ x-1` rather than introducing another series.
-/

namespace GppScalarBoxLogScaleBounds

open GppScalarBoxEndpointLinearization
open GppScalarBoxRegulatorBounds

/-- Dimensionless multiplicative correction in `a=(m/U)A`. -/
noncomputable def endpointA (η κ : ℝ) : ℝ :=
  4 * (1 - η) / (1 + κ) ^ 2

/-- For `c ≤ x ≤ 1` with `c>0`, the negative logarithm is bounded by the relative
multiplicative defect `(1-x)/c`. -/
theorem abs_log_le_one_sub_div_lower
    {c x : ℝ}
    (hc : 0 < c) (hcx : c ≤ x) (hx1 : x ≤ 1) :
    |Real.log x| ≤ (1 - x) / c := by
  have hx : 0 < x := lt_of_lt_of_le hc hcx
  have hlog : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
  have hinvlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hinvlog
  have hrewrite : x⁻¹ - 1 = (1 - x) / x := by
    field_simp [hx.ne']
  rw [hrewrite] at hinvlog
  have hnum0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hratio : (1 - x) / x ≤ (1 - x) / c := by
    exact div_le_div_of_nonneg_left hnum0 hc hcx
  rw [abs_of_nonpos hlog]
  exact hinvlog.trans hratio

/-- The elementary rationalization bound `0 ≤ κ-1 ≤ δ/2`. -/
theorem kappa_sub_one_mem
    {δ η κ : ℝ}
    (hδ0 : 0 ≤ δ) (hη0 : 0 ≤ η)
    (hκlo : 1 ≤ κ)
    (hsq : κ ^ 2 = 1 + δ * (1 - η)) :
    0 ≤ κ - 1 ∧ κ - 1 ≤ δ / 2 := by
  have he0 : 0 ≤ κ - 1 := by linarith
  have hδη0 : 0 ≤ δ * η := mul_nonneg hδ0 hη0
  have hkdiff : κ ^ 2 - 1 = δ - δ * η := by
    rw [hsq]
    ring
  have hkdiff_le : κ ^ 2 - 1 ≤ δ := by
    rw [hkdiff]
    linarith
  constructor
  · exact he0
  · nlinarith [sq_nonneg (κ - 1)]

/-- Exact factorization of the lower endpoint into its natural scale. -/
theorem a_eq_m_div_U_mul_endpointA
    {S U m κ a η : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    (hm : 0 ≤ m) (hmS : m ≤ S)
    (hκlo : 1 ≤ κ)
    (ha : a = (κ - 1) / (κ + 1))
    (hκsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U))
    (hη : η = m / S) :
    a = (m / U) * endpointA η κ := by
  have hκplus : 0 < κ + 1 := by linarith
  have hSU : S * U ≠ 0 := (mul_pos hS hU).ne'
  have haExact := a_exact_linear_m hSU hκplus.ne' ha hκsq
  rw [haExact, endpointA, hη]
  field_simp [hS.ne', hU.ne', hκplus.ne']
  ring

/-- The multiplicative correction differs from one by at most
`η + (33/64)δ`. -/
theorem one_sub_endpointA_nonneg_and_le
    {δ η κ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hκlo : 1 ≤ κ) (hκhi : κ ≤ 9 / 8)
    (hsq : κ ^ 2 = 1 + δ * (1 - η)) :
    0 ≤ 1 - endpointA η κ ∧
      1 - endpointA η κ ≤ η + (33 / 64 : ℝ) * δ := by
  have hAint := A_mem_rational_interval η κ (endpointA η κ)
    hη0 hη hκlo hκhi rfl
  rcases hAint with ⟨hAlo, hAhi⟩
  have he := kappa_sub_one_mem hδ0 hη0 hκlo hsq
  rcases he with ⟨he0, hele⟩
  let e : ℝ := κ - 1
  have he0' : 0 ≤ e := by simpa [e] using he0
  have hele' : e ≤ δ / 2 := by simpa [e] using hele
  have hsum : 0 ≤ δ / 2 + e := by positivity
  have heSqDeltaSq : e ^ 2 ≤ (δ / 2) ^ 2 := by
    have hp : 0 ≤ (δ / 2 - e) * (δ / 2 + e) :=
      mul_nonneg (sub_nonneg.mpr hele') hsum
    nlinarith
  have hδSq : δ ^ 2 ≤ δ / 4 := by
    have hp : 0 ≤ δ * (1 / 4 - δ) :=
      mul_nonneg hδ0 (sub_nonneg.mpr hδ)
    nlinarith
  have heSq : e ^ 2 ≤ δ / 16 := by
    nlinarith
  have hκplus : 0 < 1 + κ := by linarith
  have hden4 : (4 : ℝ) ≤ (1 + κ) ^ 2 := by nlinarith
  have hid :
      1 - endpointA η κ =
        (4 * η + 4 * e + e ^ 2) / (1 + κ) ^ 2 := by
    unfold endpointA
    dsimp [e]
    field_simp [hκplus.ne']
    ring
  have hnum0 : 0 ≤ 4 * η + 4 * e + e ^ 2 := by positivity
  constructor
  · exact sub_nonneg.mpr hAhi
  · rw [hid]
    calc
      (4 * η + 4 * e + e ^ 2) / (1 + κ) ^ 2 ≤
          (4 * η + 4 * e + e ^ 2) / 4 := by
        exact div_le_div_of_nonneg_left hnum0 (by norm_num) hden4
      _ ≤ η + (33 / 64 : ℝ) * δ := by
        nlinarith

/-- Quantitative lower-endpoint logarithmic scale replacement. -/
theorem abs_log_endpointA_le
    {δ η κ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hκlo : 1 ≤ κ) (hκhi : κ ≤ 9 / 8)
    (hsq : κ ^ 2 = 1 + δ * (1 - η)) :
    |Real.log (endpointA η κ)| ≤
      (289 / 192 : ℝ) * (η + (33 / 64 : ℝ) * δ) := by
  have hAint := A_mem_rational_interval η κ (endpointA η κ)
    hη0 hη hκlo hκhi rfl
  rcases hAint with ⟨hAlo, hAhi⟩
  have hdef := one_sub_endpointA_nonneg_and_le
    hδ0 hδ hη0 hη hκlo hκhi hsq
  rcases hdef with ⟨_, hdefle⟩
  have hlog := abs_log_le_one_sub_div_lower
    (c := (192 / 289 : ℝ)) (x := endpointA η κ)
    (by norm_num) hAlo hAhi
  calc
    |Real.log (endpointA η κ)| ≤
        (1 - endpointA η κ) / (192 / 289 : ℝ) := hlog
    _ ≤ (289 / 192 : ℝ) * (η + (33 / 64 : ℝ) * δ) := by
      have hconst : (0 : ℝ) ≤ 289 / 192 := by norm_num
      have := mul_le_mul_of_nonneg_left hdefle hconst
      convert this using 1 <;> ring

/-- Full logarithmic replacement for `a`: if `a=(m/U)A`, the difference between
`log a` and the natural scale `log(m/U)` is exactly controlled by `log A`. -/
theorem abs_log_a_sub_log_m_div_U_le
    {S U m κ a δ η : ℝ}
    (hS : 0 < S) (hU : 0 < U) (hm : 0 < m) (hmS : m ≤ S)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hη0 : 0 ≤ η) (hηsmall : η ≤ 1 / 4)
    (hκlo : 1 ≤ κ) (hκhi : κ ≤ 9 / 8)
    (ha : a = (κ - 1) / (κ + 1))
    (hκsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U))
    (hηdef : η = m / S)
    (hκsqScale : κ ^ 2 = 1 + δ * (1 - η)) :
    |Real.log a - Real.log (m / U)| ≤
      (289 / 192 : ℝ) * (η + (33 / 64 : ℝ) * δ) := by
  have hfac := a_eq_m_div_U_mul_endpointA
    hS hU hm.le hmS hκlo ha hκsq hηdef
  have hscale : 0 < m / U := div_pos hm hU
  have hAint := A_mem_rational_interval η κ (endpointA η κ)
    hη0 hηsmall hκlo hκhi rfl
  have hApos : 0 < endpointA η κ :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 192 / 289) hAint.1
  rw [hfac, Real.log_mul hscale.ne' hApos.ne']
  simp only [add_sub_cancel_left]
  exact abs_log_endpointA_le
    hδ0 hδ hη0 hηsmall hκlo hκhi hκsqScale

end GppScalarBoxLogScaleBounds

#print axioms GppScalarBoxLogScaleBounds.abs_log_le_one_sub_div_lower
#print axioms GppScalarBoxLogScaleBounds.kappa_sub_one_mem
#print axioms GppScalarBoxLogScaleBounds.a_eq_m_div_U_mul_endpointA
#print axioms GppScalarBoxLogScaleBounds.one_sub_endpointA_nonneg_and_le
#print axioms GppScalarBoxLogScaleBounds.abs_log_endpointA_le
#print axioms GppScalarBoxLogScaleBounds.abs_log_a_sub_log_m_div_U_le
