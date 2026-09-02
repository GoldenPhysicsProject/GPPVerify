import Mathlib.Tactic
import GppVerify.StandardModel.MassOrientationCoupling

/-!
# Exact factor-two structure of the rest Dirac clock

`MassOrientationCoupling.lean` already proves the closed-form rest evolution
and the chirality populations `cos^2(ωt)` and `sin^2(ωt)`.  This file makes
the factor two explicit at theorem level by rewriting those populations in
terms of `cos(2ωt)`, and records the half-cycle chirality exchange.
-/

namespace GppMassOrientationCoupling

/-- The left/right populations contain only the doubled angular frequency
`2ω`.  This is the precise algebraic content of the projective/observable
factor two for the rest two-state system. -/
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

/-- Starting in pure left chirality, after `π/(2ω)` the state is pure right
chirality with phase `-i`.  This is one L→R exchange; a second exchange
returns to left chirality with the deck sign `-1` at `π/ω`. -/
theorem clock_locking_half_exchange (ω : ℝ) (hω : ω ≠ 0) (χ : ℂ) :
    psiL ω χ 0 (Real.pi / (2 * ω)) = 0 ∧
    psiR ω χ 0 (Real.pi / (2 * ω)) = -Complex.I * χ := by
  have h2ω : (2 * ω) ≠ 0 := mul_ne_zero (by norm_num) hω
  have ht : ω * (Real.pi / (2 * ω)) = Real.pi / 2 := by
    field_simp
    ring
  constructor
  · simp [psiL, ht, Real.cos_pi_div_two]
  · simp [psiR, ht, Real.sin_pi_div_two]

/-- The projective population cycle closes after `π/ω`: both populations
are exactly the initial ones even though the spinor state itself has acquired
`-1` by `clock_locking_negate`. -/
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
