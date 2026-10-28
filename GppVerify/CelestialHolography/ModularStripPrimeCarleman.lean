import Mathlib

/-!
# Positive two-boundary modular strip, celestial cut, and prime-square Carleman bulk

Source: Astra, GPP-bridge work/2026-10-28_astra_celestial_modular_strip_sewing.md.
The width-pi DtN strip has a positive doubled boundary energy despite its
negative cross-face entry. That cross magnitude is exactly the celestial
two-particle cut weight divided by pi. A Carleman principal-series multiplier
receives the same-face DtN dressing to produce the celestial cut.

No arithmetic boundary intertwiner, Weil positivity or RH is asserted.
-/

namespace GppModularStripPrimeCarleman

def boundaryEnergy (D B u v : ℝ) : ℝ := D * (u ^ 2 + v ^ 2) - 2 * B * u * v

theorem energy_as_positive_squares (D B u v : ℝ) :
    boundaryEnergy D B u v = (D - B) * (u ^ 2 + v ^ 2) + B * (u - v) ^ 2 := by
  unfold boundaryEnergy
  ring

theorem energy_parity_split (D B u v : ℝ) :
    boundaryEnergy D B u v =
      (D - B) / 2 * (u + v) ^ 2 + (D + B) / 2 * (u - v) ^ 2 := by
  unfold boundaryEnergy
  ring

theorem energy_nonneg (D B u v : ℝ) (hB : 0 ≤ B) (hDB : B ≤ D) :
    0 ≤ boundaryEnergy D B u v := by
  rw [energy_as_positive_squares]
  have h1 : 0 ≤ (D - B) * (u ^ 2 + v ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hDB) (add_nonneg (sq_nonneg u) (sq_nonneg v))
  have h2 : 0 ≤ B * (u - v) ^ 2 := mul_nonneg hB (sq_nonneg _)
  linarith

theorem determinant_factorization (D B : ℝ) :
    D ^ 2 - B ^ 2 = (D - B) * (D + B) := by ring

noncomputable def normalizedSchur (D B : ℝ) : ℝ := 1 - (B / D) ^ 2

theorem normalizedSchur_nonneg (D B : ℝ) (hD : 0 < D)
    (hB : 0 ≤ B) (hBD : B ≤ D) : 0 ≤ normalizedSchur D B := by
  have hρ0 : 0 ≤ B / D := div_nonneg hB hD.le
  have hρ1 : B / D ≤ 1 := (div_le_one hD).mpr hBD
  have hp : 0 ≤ (1 - B / D) * (1 + B / D) :=
    mul_nonneg (sub_nonneg.mpr hρ1) (add_nonneg zero_le_one hρ0)
  unfold normalizedSchur
  nlinarith

noncomputable def stripDiagonal (τ : ℝ) : ℝ :=
  if τ = 0 then 1 / Real.pi
  else τ * Real.cosh (Real.pi * τ) / Real.sinh (Real.pi * τ)

noncomputable def stripCross (τ : ℝ) : ℝ :=
  if τ = 0 then 1 / Real.pi
  else τ / Real.sinh (Real.pi * τ)

noncomputable def celestialCut (τ : ℝ) : ℝ :=
  if τ = 0 then 1 else Real.pi * τ / Real.sinh (Real.pi * τ)

noncomputable def carlemanMellin (τ : ℝ) : ℝ :=
  Real.pi / (2 * Real.cosh (Real.pi * τ))

theorem celestialCut_eq_cross (τ : ℝ) :
    celestialCut τ = Real.pi * stripCross τ := by
  by_cases hτ : τ = 0
  · subst τ
    simp [celestialCut, stripCross, Real.pi_ne_zero]
  · simp only [celestialCut, stripCross, if_neg hτ]
    ring

theorem celestialCut_eq_dressed_carlemann (τ : ℝ) :
    celestialCut τ = 2 * stripDiagonal τ * carlemanMellin τ := by
  by_cases hτ : τ = 0
  · subst τ
    simp [celestialCut, stripDiagonal, carlemanMellin]
    field_simp
  · have hs : Real.sinh (Real.pi * τ) ≠ 0 :=
      Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hτ)
    have hc : Real.cosh (Real.pi * τ) ≠ 0 := (Real.cosh_pos _).ne'
    simp only [celestialCut, stripDiagonal, carlemanMellin, if_neg hτ]
    field_simp

noncomputable def evenEigen (τ : ℝ) : ℝ := stripDiagonal τ - stripCross τ
noncomputable def oddEigen (τ : ℝ) : ℝ := stripDiagonal τ + stripCross τ

theorem stripCross_nonneg_of_pos (τ : ℝ) (hτ : 0 < τ) :
    0 ≤ stripCross τ := by
  have hs : 0 < Real.sinh (Real.pi * τ) :=
    Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hτ)
  simp only [stripCross, if_neg hτ.ne']
  exact div_nonneg hτ.le hs.le

theorem stripCross_le_diagonal_of_pos (τ : ℝ) (hτ : 0 < τ) :
    stripCross τ ≤ stripDiagonal τ := by
  have hs : 0 < Real.sinh (Real.pi * τ) :=
    Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hτ)
  have hc : 1 ≤ Real.cosh (Real.pi * τ) := Real.one_le_cosh _
  have hnum : τ ≤ τ * Real.cosh (Real.pi * τ) := by
    nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hc)]
  simp only [stripCross, stripDiagonal, if_neg hτ.ne']
  exact (div_le_div_iff₀ hs hs).mpr (by nlinarith [hnum])

theorem strip_energy_nonneg_of_pos (τ : ℝ) (hτ : 0 < τ) (u v : ℝ) :
    0 ≤ boundaryEnergy (stripDiagonal τ) (stripCross τ) u v :=
  energy_nonneg _ _ _ _ (stripCross_nonneg_of_pos τ hτ)
    (stripCross_le_diagonal_of_pos τ hτ)

theorem zero_mode_energy (u v : ℝ) :
    boundaryEnergy (stripDiagonal 0) (stripCross 0) u v = (u - v) ^ 2 / Real.pi := by
  simp [boundaryEnergy, stripDiagonal, stripCross]
  ring

theorem celestialCut_eq_parity_gap (τ : ℝ) :
    celestialCut τ = Real.pi / 2 * (oddEigen τ - evenEigen τ) := by
  rw [celestialCut_eq_cross]
  unfold oddEigen evenEigen
  ring

theorem shadow_connection_eq_diagonal_ratio (τ : ℝ) (hτ : τ ≠ 0) :
    Real.tanh (Real.pi * τ) = τ / stripDiagonal τ := by
  have hs : Real.sinh (Real.pi * τ) ≠ 0 :=
    Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hτ)
  have hc : Real.cosh (Real.pi * τ) ≠ 0 := (Real.cosh_pos _).ne'
  simp only [stripDiagonal, if_neg hτ, Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem cross_ratio_eq_sech (τ : ℝ) (hτ : τ ≠ 0) :
    stripCross τ / stripDiagonal τ = (Real.cosh (Real.pi * τ))⁻¹ := by
  have hs : Real.sinh (Real.pi * τ) ≠ 0 :=
    Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hτ)
  have hc : Real.cosh (Real.pi * τ) ≠ 0 := (Real.cosh_pos _).ne'
  simp only [stripDiagonal, stripCross, if_neg hτ]
  field_simp

theorem normalizedSchur_eq_tanh_sq (τ : ℝ) :
    normalizedSchur (stripDiagonal τ) (stripCross τ) =
      Real.tanh (Real.pi * τ) ^ 2 := by
  by_cases hτ : τ = 0
  · subst τ
    simp [normalizedSchur, stripDiagonal, stripCross, Real.pi_ne_zero]
  · rw [normalizedSchur, cross_ratio_eq_sech τ hτ, Real.tanh_eq_sinh_div_cosh]
    have hc : Real.cosh (Real.pi * τ) ≠ 0 := (Real.cosh_pos _).ne'
    have hsq := Real.cosh_sq (Real.pi * τ)
    field_simp
    nlinarith

end GppModularStripPrimeCarleman

#print axioms GppModularStripPrimeCarleman.energy_nonneg
#print axioms GppModularStripPrimeCarleman.celestialCut_eq_dressed_carlemann
#print axioms GppModularStripPrimeCarleman.normalizedSchur_eq_tanh_sq
