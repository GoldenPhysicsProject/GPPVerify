import GppVerify.CelestialHolography.ScalarBoxEndpointLinearization
import GppVerify.CelestialHolography.ScalarBoxLogScaleBounds
import Mathlib.Tactic

/-!
# Logarithmic scale of the scalar-box upper Mobius endpoint

Write `rho = m/U` and

  q = rho * Q,   Q = (2R/(1+R))^2.

On the physical chamber `8/9 <= R <= 1` one has `256/289 <= Q <= 1` and
`1-Q <= 2q`. Combined with the certified linear bound
`q <= (324/289) rho`, this gives the exact coarse estimate

  |log q| <= |log rho| + (81/32) rho.
-/

namespace GppScalarBoxQLogScale

open GppScalarBoxEndpointLinearization
open GppScalarBoxLogScaleBounds

/-- Unit-centered correction in `q = rho * Q`. -/
noncomputable def endpointQ (R : ℝ) : ℝ :=
  (2 * R / (1 + R)) ^ 2

/-- Exact factorization of the upper Mobius endpoint into its natural scale. -/
theorem q_eq_rho_mul_endpointQ
    {U m R q ρ : ℝ}
    (hU : 0 < U) (hm : 0 ≤ m)
    (hRlo : 8 / 9 ≤ R)
    (hq : q = (1 - R) / (1 + R))
    (hRsq : R ^ 2 = U / (U + 4 * m))
    (hρ : ρ = m / U) :
    q = ρ * endpointQ R := by
  have hU4 : 0 < U + 4 * m := by positivity
  have hRplus : 0 < 1 + R := by linarith
  have hqexact := q_exact_linear_m hU4.ne' hRplus.ne' hq hRsq
  have hQ : endpointQ R = 4 * R ^ 2 / (1 + R) ^ 2 := by
    unfold endpointQ
    field_simp [hRplus.ne']
    ring
  rw [hqexact, hρ, hQ, hRsq]
  field_simp [hU.ne', hU4.ne', hRplus.ne']
  ring

/-- On `8/9 <= R <= 1`, the normalization factor is in `[256/289,1]`. -/
theorem endpointQ_mem
    {R : ℝ} (hRlo : 8 / 9 ≤ R) (hRhi : R ≤ 1) :
    256 / 289 ≤ endpointQ R ∧ endpointQ R ≤ 1 := by
  have hR0 : 0 ≤ R := by linarith
  have hplus : 0 < 1 + R := by linarith
  unfold endpointQ
  constructor
  · have hfrac : (16 / 17 : ℝ) ≤ 2 * R / (1 + R) := by
      apply (le_div_iff₀ hplus).2
      nlinarith
    have hfrac0 : 0 ≤ 2 * R / (1 + R) := div_nonneg (by positivity) hplus.le
    nlinarith [sq_nonneg (2 * R / (1 + R) - 16 / 17)]
  · have hfrac : 2 * R / (1 + R) ≤ 1 := by
      apply (div_le_iff₀ hplus).2
      linarith
    have hfrac0 : 0 ≤ 2 * R / (1 + R) := div_nonneg (by positivity) hplus.le
    nlinarith

/-- Exact relative defect identity. -/
theorem one_sub_endpointQ_eq_q_factor
    {R q : ℝ}
    (hRplus : 1 + R ≠ 0)
    (hq : q = (1 - R) / (1 + R)) :
    1 - endpointQ R = q * ((1 + 3 * R) / (1 + R)) := by
  unfold endpointQ
  rw [hq]
  field_simp [hRplus]
  ring

/-- On the physical chamber the normalization defect is at most twice `q`. -/
theorem one_sub_endpointQ_le_two_q
    {R q : ℝ}
    (hRlo : 8 / 9 ≤ R) (hRhi : R ≤ 1)
    (hq0 : 0 ≤ q)
    (hq : q = (1 - R) / (1 + R)) :
    1 - endpointQ R ≤ 2 * q := by
  have hplus : 0 < 1 + R := by linarith
  rw [one_sub_endpointQ_eq_q_factor hplus.ne' hq]
  have hfac : (1 + 3 * R) / (1 + R) ≤ 2 := by
    apply (div_le_iff₀ hplus).2
    linarith
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hfac hq0

/-- The unit-centered correction contributes at most `(81/32) rho` to the log. -/
theorem abs_log_endpointQ_le
    {R q ρ : ℝ}
    (hRlo : 8 / 9 ≤ R) (hRhi : R ≤ 1)
    (hρ0 : 0 ≤ ρ)
    (hq0 : 0 ≤ q)
    (hqρ : q ≤ (324 / 289 : ℝ) * ρ)
    (hq : q = (1 - R) / (1 + R)) :
    |Real.log (endpointQ R)| ≤ (81 / 32 : ℝ) * ρ := by
  rcases endpointQ_mem hRlo hRhi with ⟨hQlo, hQhi⟩
  have hlog := abs_log_le_one_sub_div_lower
    (c := (256 / 289 : ℝ)) (x := endpointQ R)
    (by norm_num) hQlo hQhi
  have hdef := one_sub_endpointQ_le_two_q hRlo hRhi hq0 hq
  calc
    |Real.log (endpointQ R)| ≤
        (1 - endpointQ R) / (256 / 289 : ℝ) := hlog
    _ ≤ (2 * q) / (256 / 289 : ℝ) := by
      exact div_le_div_of_nonneg_right hdef (by norm_num)
    _ ≤ (81 / 32 : ℝ) * ρ := by
      have hm := mul_le_mul_of_nonneg_left hqρ (by norm_num : (0 : ℝ) ≤ 289 / 128)
      convert hm using 1 <;> ring

/-- Final physical logarithmic scale estimate for `q`. -/
theorem abs_log_q_le_abs_log_rho_add
    {U m R q ρ : ℝ}
    (hU : 0 < U) (hm : 0 < m) (hmU : m ≤ U / 16)
    (hRlo : 8 / 9 ≤ R) (hRhi : R ≤ 1)
    (hq : q = (1 - R) / (1 + R))
    (hRsq : R ^ 2 = U / (U + 4 * m))
    (hρ : ρ = m / U) :
    |Real.log q| ≤ |Real.log ρ| + (81 / 32 : ℝ) * ρ := by
  have hρpos : 0 < ρ := by rw [hρ]; exact div_pos hm hU
  have hρ0 : 0 ≤ ρ := hρpos.le
  have hqpair := q_nonneg_and_le_linear_m hU hm.le hRlo hq hRsq
  have hq0 : 0 ≤ q := hqpair.1
  have hqρ : q ≤ (324 / 289 : ℝ) * ρ := by simpa [hρ] using hqpair.2
  have hQmem := endpointQ_mem hRlo hRhi
  have hQpos : 0 < endpointQ R := lt_of_lt_of_le (by norm_num) hQmem.1
  have hfac := q_eq_rho_mul_endpointQ hU hm.le hRlo hq hRsq hρ
  have hlogQ := abs_log_endpointQ_le hRlo hRhi hρ0 hq0 hqρ hq
  rw [hfac, Real.log_mul hρpos.ne' hQpos.ne']
  exact (abs_add _ _).trans (add_le_add_left hlogQ _)

end GppScalarBoxQLogScale

#print axioms GppScalarBoxQLogScale.q_eq_rho_mul_endpointQ
#print axioms GppScalarBoxQLogScale.endpointQ_mem
#print axioms GppScalarBoxQLogScale.one_sub_endpointQ_eq_q_factor
#print axioms GppScalarBoxQLogScale.one_sub_endpointQ_le_two_q
#print axioms GppScalarBoxQLogScale.abs_log_endpointQ_le
#print axioms GppScalarBoxQLogScale.abs_log_q_le_abs_log_rho_add
