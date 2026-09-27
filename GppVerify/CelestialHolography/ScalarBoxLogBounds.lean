import GppVerify.CelestialHolography.ScalarBoxRegulatorBounds
import GppVerify.CelestialHolography.ScalarBoxEndpointLinearization
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

/-!
# Elementary logarithm bounds for the scalar-box regulator

Mathlib already proves a sharp local Taylor bound for the complex logarithm. Restricting
that theorem to a positive real segment yields the real estimate needed for the
regulated scalar-box endpoint errors, without introducing a separate logarithm series.
-/

namespace GppScalarBoxLogBounds

open GppScalarBoxEndpointLinearization

/-- For `0 ≤ x ≤ 1/2`, the real logarithm obeys the uniform local estimate
`|log(1-x)| ≤ (3/2)x`. -/
theorem abs_log_one_sub_le_three_halves
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ (3 / 2 : ℝ) * x := by
  have hz : ‖(-(x : ℂ))‖ ≤ (1 / 2 : ℝ) := by
    simpa [Complex.norm_real, abs_of_nonneg hx0] using hx
  have h := Complex.norm_log_one_add_half_le_self hz
  have hpos : 0 ≤ 1 - x := by linarith
  have hlog : Complex.log ((1 - x : ℝ) : ℂ) = (Real.log (1 - x) : ℂ) := by
    simpa using (Complex.ofReal_log hpos).symm
  have hone : (1 : ℂ) + (-(x : ℂ)) = ((1 - x : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hone, hlog] at h
  simpa [Complex.norm_real, abs_of_nonneg hx0] using h

/-- A convenient squared consequence used for the lower endpoint remainder. -/
theorem half_log_one_sub_sq_le
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 / 2 : ℝ) * (Real.log (1 - x)) ^ 2 ≤ (9 / 8 : ℝ) * x ^ 2 := by
  have h := abs_log_one_sub_le_three_halves hx0 hx
  have hrhs0 : 0 ≤ (3 / 2 : ℝ) * x := by positivity
  have habs0 : 0 ≤ |Real.log (1 - x)| := abs_nonneg _
  have hdiff :
      0 ≤ (3 / 2 : ℝ) * x - |Real.log (1 - x)| :=
    sub_nonneg.mpr h
  have hsum :
      0 ≤ (3 / 2 : ℝ) * x + |Real.log (1 - x)| :=
    add_nonneg hrhs0 habs0
  have hprod :
      0 ≤ ((3 / 2 : ℝ) * x - |Real.log (1 - x)|) *
        ((3 / 2 : ℝ) * x + |Real.log (1 - x)|) :=
    mul_nonneg hdiff hsum
  have hsquareAbs :
      |Real.log (1 - x)| ^ 2 ≤ ((3 / 2 : ℝ) * x) ^ 2 := by
    nlinarith
  have habsSq : |Real.log (1 - x)| ^ 2 = (Real.log (1 - x)) ^ 2 := by
    rw [sq_abs]
  rw [habsSq] at hsquareAbs
  nlinarith

/-- The scalar-box lower endpoint inherits a linear logarithmic regulator bound.
Under `m ≤ U/2`, the certified endpoint estimate `a ≤ m/U` keeps `a` inside the
local logarithm disk and gives

`|log(1-a)| ≤ (3/2) m/U`.
-/
theorem abs_log_one_sub_a_le_linear_m
    {S U m κ a : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    (hm0 : 0 ≤ m) (hmS : m ≤ S) (hmU : m ≤ U / 2)
    (hκlo : 1 ≤ κ)
    (ha : a = (κ - 1) / (κ + 1))
    (hsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U)) :
    |Real.log (1 - a)| ≤ (3 / 2 : ℝ) * (m / U) := by
  rcases a_nonneg_and_le_linear_m hS hU hm0 hmS hκlo ha hsq with ⟨ha0, hale⟩
  have hmUhalf : m / U ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hU).2
    nlinarith
  have hahalf : a ≤ (1 / 2 : ℝ) := hale.trans hmUhalf
  calc
    |Real.log (1 - a)| ≤ (3 / 2 : ℝ) * a :=
      abs_log_one_sub_le_three_halves ha0 hahalf
    _ ≤ (3 / 2 : ℝ) * (m / U) := by
      exact mul_le_mul_of_nonneg_left hale (by norm_num)

/-- Squared lower-endpoint logarithmic error at the natural regulator scale. -/
theorem half_log_one_sub_a_sq_le_linear_m_sq
    {S U m κ a : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    (hm0 : 0 ≤ m) (hmS : m ≤ S) (hmU : m ≤ U / 2)
    (hκlo : 1 ≤ κ)
    (ha : a = (κ - 1) / (κ + 1))
    (hsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U)) :
    (1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2 ≤
      (9 / 8 : ℝ) * (m / U) ^ 2 := by
  rcases a_nonneg_and_le_linear_m hS hU hm0 hmS hκlo ha hsq with ⟨ha0, hale⟩
  have hmUhalf : m / U ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hU).2
    nlinarith
  have hahalf : a ≤ (1 / 2 : ℝ) := hale.trans hmUhalf
  calc
    (1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2 ≤ (9 / 8 : ℝ) * a ^ 2 :=
      half_log_one_sub_sq_le ha0 hahalf
    _ ≤ (9 / 8 : ℝ) * (m / U) ^ 2 := by
      have hsquare : a ^ 2 ≤ (m / U) ^ 2 := by
        nlinarith [sq_nonneg ((m / U) - a)]
      exact mul_le_mul_of_nonneg_left hsquare (by norm_num)

end GppScalarBoxLogBounds

#print axioms GppScalarBoxLogBounds.abs_log_one_sub_le_three_halves
#print axioms GppScalarBoxLogBounds.half_log_one_sub_sq_le
#print axioms GppScalarBoxLogBounds.abs_log_one_sub_a_le_linear_m
#print axioms GppScalarBoxLogBounds.half_log_one_sub_a_sq_le_linear_m_sq
