import Mathlib.Tactic
import GppVerify.StandardModel.MassOrientationCoupling

namespace GppMassOrientationCoupling

theorem clock_locking_population_double_frequency (ω : ℝ) (χ : ℂ) (t : ℝ) :
    Complex.normSq (psiL ω χ 0 t)
        = ((1 + Real.cos (2 * (ω * t))) / 2) * Complex.normSq χ ∧
    Complex.normSq (psiR ω χ 0 t)
        = ((1 - Real.cos (2 * (ω * t))) / 2) * Complex.normSq χ := by
  obtain ⟨hL, hR⟩ := clock_locking_population ω χ t
  constructor
  · rw [hL, Real.cos_two_mul]
    ring
  · rw [hR, Real.cos_two_mul]
    have htrig := Real.sin_sq_add_cos_sq (ω * t)
    nlinarith

theorem clock_locking_half_exchange (ω : ℝ) (hω : ω ≠ 0) (χ : ℂ) :
    psiL ω χ 0 (Real.pi / (2 * ω)) = 0 ∧
    psiR ω χ 0 (Real.pi / (2 * ω)) = -Complex.I * χ := by
  have ht : ω * (Real.pi / (2 * ω)) = Real.pi / 2 := by
    field_simp
    ring
  constructor
  · simp [psiL, ht, Real.cos_pi_div_two]
  · simp [psiR, ht, Real.sin_pi_div_two]

theorem clock_locking_projective_period (ω : ℝ) (hω : ω ≠ 0) (χ : ℂ) :
    Complex.normSq (psiL ω χ 0 (Real.pi / ω)) = Complex.normSq χ ∧
    Complex.normSq (psiR ω χ 0 (Real.pi / ω)) = 0 := by
  obtain ⟨hstateL, hstateR⟩ := clock_locking_negate ω hω χ 0
  constructor
  · rw [hstateL]
    simp
  · rw [hstateR]
    simp

end GppMassOrientationCoupling
