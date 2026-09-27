import GppVerify.CelestialHolography.ScalarBoxStructuredRemainder
import Mathlib.Tactic

/-!
# Scalar-box prefactor remainder

The regulated scalar box carries an additional factor `1/κ`.  On the physical
small-regulator chamber the already established estimate `0 ≤ κ-1 ≤ δ/2` makes this
prefactor correction quantitatively harmless.  This file isolates that algebra from
the special-function remainder.
-/

namespace GppScalarBoxPrefactorRemainder

/-- If `1 ≤ κ` and `κ-1 ≤ δ/2`, then the inverse prefactor differs from one by at
most `δ/2`. -/
theorem abs_inv_kappa_sub_one_le
    {κ δ : ℝ}
    (hκ : 1 ≤ κ)
    (hκdiff : κ - 1 ≤ δ / 2) :
    |1 / κ - 1| ≤ δ / 2 := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hdiff0 : 0 ≤ κ - 1 := by linarith
  have hinvle : 1 / κ ≤ 1 := by
    apply (div_le_iff₀ hκpos).2
    simpa using hκ
  have habs : |1 / κ - 1| = (κ - 1) / κ := by
    rw [abs_of_nonpos (sub_nonpos.mpr hinvle)]
    field_simp [hκpos.ne']
  rw [habs]
  exact (div_le_self hdiff0 hκ).trans hκdiff

/-- The defining physical relation for `κ²` itself supplies the prefactor estimate.
For `0 ≤ m ≤ S`, `U>0`, and `κ≥1`, one has

`κ - 1 ≤ 2m/U = (4m/U)/2`.

Thus no independent asymptotic hypothesis on the inverse prefactor is needed. -/
theorem kappa_sub_one_le_two_mul_m_div_U
    {S U m κ : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    (hm0 : 0 ≤ m) (hmS : m ≤ S)
    (hκ : 1 ≤ κ)
    (hκsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U)) :
    κ - 1 ≤ 2 * m / U := by
  have hSU : 0 < S * U := mul_pos hS hU
  have hsqdiff : κ ^ 2 - 1 = 4 * m * (S - m) / (S * U) := by
    rw [hκsq]
    ring
  have hrhsle : 4 * m * (S - m) / (S * U) ≤ 4 * m / U := by
    rw [div_le_iff₀ hSU]
    have hright : (4 * m / U) * (S * U) = 4 * m * S := by
      field_simp [hU.ne']
      ring
    rw [hright]
    nlinarith [sq_nonneg m]
  have hprodlo : 2 * (κ - 1) ≤ (κ - 1) * (κ + 1) := by
    have hk0 : 0 ≤ κ - 1 := by linarith
    have hkplus : 2 ≤ κ + 1 := by linarith
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hkplus hk0
  have hprodhi : (κ - 1) * (κ + 1) ≤ 4 * m / U := by
    calc
      (κ - 1) * (κ + 1) = κ ^ 2 - 1 := by ring
      _ = 4 * m * (S - m) / (S * U) := hsqdiff
      _ ≤ 4 * m / U := hrhsle
  have htwo : 2 * (κ - 1) ≤ 4 * m / U := hprodlo.trans hprodhi
  have hhalf := (div_le_div_iff_of_pos_right (show (0 : ℝ) < 2 by norm_num)).2 htwo
  convert hhalf using 1 <;> ring

/-- Exact decomposition of the prefactor-corrected remainder. -/
theorem prefactor_remainder_identity
    {D D0 κ : ℝ} (hκ : κ ≠ 0) :
    D / κ - D0 = (D - D0) / κ + (1 / κ - 1) * D0 := by
  field_simp [hκ]
  ring

/-- The prefactor correction adds at most `(δ/2)|D0|` to any core remainder bound. -/
theorem abs_prefactor_remainder_le
    {D D0 κ δ : ℝ}
    (hκ : 1 ≤ κ)
    (hκdiff : κ - 1 ≤ δ / 2) :
    |D / κ - D0| ≤ |D - D0| + (δ / 2) * |D0| := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hinv := abs_inv_kappa_sub_one_le hκ hκdiff
  have hcore : |D - D0| / κ ≤ |D - D0| :=
    div_le_self (abs_nonneg _) hκ
  rw [prefactor_remainder_identity hκpos.ne']
  calc
    |(D - D0) / κ + (1 / κ - 1) * D0| ≤
        |(D - D0) / κ| + |(1 / κ - 1) * D0| := abs_add _ _
    _ = |D - D0| / κ + |1 / κ - 1| * |D0| := by
      rw [abs_div, abs_of_pos hκpos, abs_mul]
    _ ≤ |D - D0| + (δ / 2) * |D0| := by
      gcongr

/-- Plugging any certified structured core majorant into the prefactor estimate yields
the final algebraic envelope before the overall `2/(SU)` normalization. -/
theorem abs_prefactor_remainder_le_of_core_bound
    {D D0 κ δ M : ℝ}
    (hκ : 1 ≤ κ)
    (hκdiff : κ - 1 ≤ δ / 2)
    (hcore : |D - D0| ≤ M) :
    |D / κ - D0| ≤ M + (δ / 2) * |D0| := by
  exact (abs_prefactor_remainder_le hκ hκdiff).trans
    (add_le_add_right hcore ((δ / 2) * |D0|))

/-- Physical specialization: the quadratic definition of `κ` discharges the
prefactor hypothesis automatically. -/
theorem abs_prefactor_remainder_le_of_physical_core_bound
    {S U m D D0 κ M : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    (hm0 : 0 ≤ m) (hmS : m ≤ S)
    (hκ : 1 ≤ κ)
    (hκsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U))
    (hcore : |D - D0| ≤ M) :
    |D / κ - D0| ≤ M + ((4 * m / U) / 2) * |D0| := by
  apply abs_prefactor_remainder_le_of_core_bound hκ
  · have h := kappa_sub_one_le_two_mul_m_div_U hS hU hm0 hmS hκ hκsq
    convert h using 1 <;> ring
  · exact hcore

end GppScalarBoxPrefactorRemainder

#print axioms GppScalarBoxPrefactorRemainder.abs_inv_kappa_sub_one_le
#print axioms GppScalarBoxPrefactorRemainder.kappa_sub_one_le_two_mul_m_div_U
#print axioms GppScalarBoxPrefactorRemainder.prefactor_remainder_identity
#print axioms GppScalarBoxPrefactorRemainder.abs_prefactor_remainder_le
#print axioms GppScalarBoxPrefactorRemainder.abs_prefactor_remainder_le_of_core_bound
#print axioms GppScalarBoxPrefactorRemainder.abs_prefactor_remainder_le_of_physical_core_bound
