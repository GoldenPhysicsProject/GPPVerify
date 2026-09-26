import GppVerify.CelestialHolography.ScalarBoxRegulatorAlgebra
import Mathlib.Tactic

/-!
# Exact linear regulator factors for scalar-box Möbius endpoints

The regulated box uses

  q = (1-R)/(1+R),      a = (κ-1)/(κ+1).

The quadratic defining relations for `R` and `κ` can be rationalized before any
asymptotic estimate is taken.  This exposes one exact factor of the regulator `m`
in each endpoint.  Together with the already-certified quadratic estimate for `q-a`,
these identities isolate the hierarchy needed for the final logarithmic remainder.
-/

namespace GppScalarBoxEndpointLinearization

/-- Rationalizing `R² = U/(U+4m)` exposes an exact factor of `m` in the Möbius
endpoint `q=(1-R)/(1+R)`. -/
theorem q_exact_linear_m
    {U m R q : ℝ}
    (hU4 : U + 4 * m ≠ 0)
    (hRplus : 1 + R ≠ 0)
    (hq : q = (1 - R) / (1 + R))
    (hsq : R ^ 2 = U / (U + 4 * m)) :
    q = 4 * m / ((U + 4 * m) * (1 + R) ^ 2) := by
  have hsq' : R ^ 2 * (U + 4 * m) = U := (eq_div_iff hU4).mp hsq
  rw [hq]
  field_simp [hRplus, hU4]
  nlinarith

/-- On the physical small-regulator interval, `q` is nonnegative and linearly small:
`0 ≤ q ≤ (324/289) m/U`. -/
theorem q_nonneg_and_le_linear_m
    {U m R q : ℝ}
    (hU : 0 < U) (hm0 : 0 ≤ m)
    (hRlo : 8 / 9 ≤ R)
    (hq : q = (1 - R) / (1 + R))
    (hsq : R ^ 2 = U / (U + 4 * m)) :
    0 ≤ q ∧ q ≤ (324 / 289 : ℝ) * (m / U) := by
  have hU4pos : 0 < U + 4 * m := by positivity
  have hRpluspos : 0 < 1 + R := by linarith
  have hqexact := q_exact_linear_m hU4pos.ne' hRpluspos.ne' hq hsq
  rw [hqexact]
  have hdenpos : 0 < (U + 4 * m) * (1 + R) ^ 2 := by positivity
  have hRfac : (17 / 9 : ℝ) ≤ 1 + R := by linarith
  have hsqfac : (289 / 81 : ℝ) ≤ (1 + R) ^ 2 := by nlinarith
  have hU4ge : U ≤ U + 4 * m := by linarith
  have hdenlower : U * (289 / 81 : ℝ) ≤ (U + 4 * m) * (1 + R) ^ 2 := by
    calc
      U * (289 / 81 : ℝ) ≤ (U + 4 * m) * (289 / 81 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hU4ge (by norm_num)
      _ ≤ (U + 4 * m) * (1 + R) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsqfac hU4pos.le
  have hbasepos : 0 < U * (289 / 81 : ℝ) := by positivity
  constructor
  · exact div_nonneg (by positivity) hdenpos.le
  · have hnum0 : 0 ≤ 4 * m := by positivity
    calc
      4 * m / ((U + 4 * m) * (1 + R) ^ 2) ≤
          4 * m / (U * (289 / 81 : ℝ)) := by
            exact div_le_div_of_nonneg_left hnum0 hbasepos hdenlower
      _ = (324 / 289 : ℝ) * (m / U) := by
            field_simp [hU.ne']
            ring

/-- Rationalizing `κ² = 1 + 4m(S-m)/(SU)` exposes an exact factor of `m` in
`a=(κ-1)/(κ+1)`. -/
theorem a_exact_linear_m
    {S U m κ a : ℝ}
    (hSU : S * U ≠ 0)
    (hκplus : κ + 1 ≠ 0)
    (ha : a = (κ - 1) / (κ + 1))
    (hsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U)) :
    a = 4 * m * (S - m) / ((S * U) * (κ + 1) ^ 2) := by
  have hfac0 : κ ^ 2 * (S * U) - S * U = 4 * m * (S - m) := by
    have h := hsq
    field_simp [hSU] at h
    nlinarith
  have hfac : (κ - 1) * (κ + 1) * (S * U) = 4 * m * (S - m) := by
    calc
      (κ - 1) * (κ + 1) * (S * U) = κ ^ 2 * (S * U) - S * U := by ring
      _ = 4 * m * (S - m) := hfac0
  have hden : (S * U) * (κ + 1) ^ 2 ≠ 0 :=
    mul_ne_zero hSU (pow_ne_zero 2 hκplus)
  apply (eq_div_iff hden).2
  rw [ha]
  calc
    (κ - 1) / (κ + 1) * ((S * U) * (κ + 1) ^ 2) =
        (κ - 1) * (κ + 1) * (S * U) := by
          field_simp [hκplus]
          ring
    _ = 4 * m * (S - m) := hfac

/-- On the physical interval `0 ≤ m ≤ S`, the lower endpoint satisfies the sharp
linear estimate `0 ≤ a ≤ m/U`. -/
theorem a_nonneg_and_le_linear_m
    {S U m κ a : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    (hm0 : 0 ≤ m) (hmS : m ≤ S)
    (hκlo : 1 ≤ κ)
    (ha : a = (κ - 1) / (κ + 1))
    (hsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U)) :
    0 ≤ a ∧ a ≤ m / U := by
  have hSUpos : 0 < S * U := mul_pos hS hU
  have hκplus : 0 < κ + 1 := by linarith
  have haexact := a_exact_linear_m hSUpos.ne' hκplus.ne' ha hsq
  rw [haexact]
  have hSm : 0 ≤ S - m := by linarith
  have hnum0 : 0 ≤ 4 * m * (S - m) := by positivity
  have hnumle : 4 * m * (S - m) ≤ 4 * m * S := by
    nlinarith [sq_nonneg m]
  have hκfac : (4 : ℝ) ≤ (κ + 1) ^ 2 := by
    have hfac : 0 ≤ (κ - 1) * (κ + 3) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hdenlower : 4 * (S * U) ≤ (S * U) * (κ + 1) ^ 2 := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hκfac hSUpos.le
  have hbasepos : 0 < 4 * (S * U) := by positivity
  have hdenpos : 0 < (S * U) * (κ + 1) ^ 2 := by positivity
  have hnumUpper0 : 0 ≤ 4 * m * S := by positivity
  constructor
  · exact div_nonneg hnum0 hdenpos.le
  · calc
      4 * m * (S - m) / ((S * U) * (κ + 1) ^ 2) ≤
          (4 * m * S) / ((S * U) * (κ + 1) ^ 2) := by
            exact div_le_div_of_nonneg_right hnumle hdenpos.le
      _ ≤ (4 * m * S) / (4 * (S * U)) := by
            exact div_le_div_of_nonneg_left hnumUpper0 hbasepos hdenlower
      _ = m / U := by
            field_simp [hS.ne', hU.ne']
            ring

end GppScalarBoxEndpointLinearization

#print axioms GppScalarBoxEndpointLinearization.q_exact_linear_m
#print axioms GppScalarBoxEndpointLinearization.q_nonneg_and_le_linear_m
#print axioms GppScalarBoxEndpointLinearization.a_exact_linear_m
#print axioms GppScalarBoxEndpointLinearization.a_nonneg_and_le_linear_m
