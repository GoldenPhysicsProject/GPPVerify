import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Euler-local Poisson kernel and the positive valuation-chain Laplacian

For one degree-one Euler factor, put 0 <= q < 1 (arithmetically
q = p^(-1/2)) and

  P_q(theta) = (1-q^2)/(1-2q cos(theta)+q^2).

The coherent prime-power tower has Fourier density P_q. This file records
the exact algebra that separates its positive graph-Laplacian part from the
sign-indefinite centered current:

  (1+q)/(1-q) - P_q(theta) >= 0,

whereas

  1 - P_q(theta) = 2q(q-cos(theta))/(1-2q cos(theta)+q^2)

has no fixed sign.

This is the local algebra behind the distinction between the positive
valuation-chain parent and the RH-bearing prime--Archimedean centered form.
No zeta-zero or RH statement is made here.
-/

namespace GppEulerLocalPoisson

/-- Denominator of the Poisson kernel. -/
noncomputable def poissonDenom (q theta : ℝ) : ℝ :=
  1 - 2 * q * Real.cos theta + q ^ 2

/-- The usual disk Poisson kernel at radial coordinate q. -/
noncomputable def poissonKernel (q theta : ℝ) : ℝ :=
  (1 - q ^ 2) / poissonDenom q theta

/-- The denominator is a square plus the nonnegative angular defect. -/
theorem poissonDenom_square (q theta : ℝ) :
    poissonDenom q theta = (1 - q) ^ 2 + 2 * q * (1 - Real.cos theta) := by
  unfold poissonDenom
  ring

/-- For 0 <= q < 1, the Poisson denominator is strictly positive. -/
theorem poissonDenom_pos {q theta : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 < poissonDenom q theta := by
  rw [poissonDenom_square]
  have hc : 0 ≤ 1 - Real.cos theta := sub_nonneg.mpr (Real.cos_le_one theta)
  have hs : 0 < (1 - q) ^ 2 := sq_pos_of_pos (sub_pos.mpr hq1)
  nlinarith [mul_nonneg hq0 hc]

/-- Exact closed form of the coherent local Laplacian multiplier. -/
theorem laplacian_gap_identity {q theta : ℝ} (hq : q ≠ 1)
    (hden : poissonDenom q theta ≠ 0) :
    (1 + q) / (1 - q) - poissonKernel q theta =
      (2 * q * (1 + q) * (1 - Real.cos theta)) /
        ((1 - q) * poissonDenom q theta) := by
  unfold poissonKernel
  field_simp [hq, hden]
  unfold poissonDenom
  ring

/-- The coherent local valuation-chain Laplacian is nonnegative. -/
theorem laplacian_gap_nonneg {q theta : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ (1 + q) / (1 - q) - poissonKernel q theta := by
  have hq : q ≠ 1 := ne_of_lt hq1
  have hdpos : 0 < poissonDenom q theta := poissonDenom_pos hq0 hq1
  rw [laplacian_gap_identity hq hdpos.ne']
  have h1mq : 0 < 1 - q := sub_pos.mpr hq1
  have h1pq : 0 < 1 + q := by linarith
  have hc : 0 ≤ 1 - Real.cos theta := sub_nonneg.mpr (Real.cos_le_one theta)
  positivity

/-- The centered local current is the Poisson kernel minus its unit baseline.
Its sign depends on whether cos(theta) lies above or below q. -/
theorem centered_current_identity {q theta : ℝ}
    (hden : poissonDenom q theta ≠ 0) :
    1 - poissonKernel q theta =
      (2 * q * (q - Real.cos theta)) / poissonDenom q theta := by
  unfold poissonKernel
  field_simp [hden]
  unfold poissonDenom
  ring

/-- At zero phase the Poisson kernel attains the valuation-chain endpoint value. -/
theorem poissonKernel_zero {q : ℝ} (hq : q ≠ 1) :
    poissonKernel q 0 = (1 + q) / (1 - q) := by
  unfold poissonKernel poissonDenom
  simp only [Real.cos_zero]
  field_simp [hq]
  ring

/-- Consequently the positive local Laplacian has its exact zero mode at zero phase. -/
theorem laplacian_gap_zero {q : ℝ} (hq : q ≠ 1) :
    (1 + q) / (1 - q) - poissonKernel q 0 = 0 := by
  rw [poissonKernel_zero hq]
  ring

end GppEulerLocalPoisson

#print axioms GppEulerLocalPoisson.poissonDenom_pos
#print axioms GppEulerLocalPoisson.laplacian_gap_identity
#print axioms GppEulerLocalPoisson.laplacian_gap_nonneg
#print axioms GppEulerLocalPoisson.centered_current_identity
