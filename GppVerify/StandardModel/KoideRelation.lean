import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The Koide relation's SU(3) phase sum, and ε = √2

Source: ONON5213.tex, "The Koide Structure: √2 as a Theorem"
(sec:koide). Three generations sit at phases `2πg/3` (g = 0,1,2), the
Weyl orbit of SU(3)_F. The derivation of the Koide ratio
`Q = (1 + ε²/2)/3` uses two trigonometric sum facts:
`Σ_g cos(2πg/3 - δ) = 0` and `Σ_g cos²(2πg/3 - δ) = 3/2`.

This file formalizes the first (linear) phase-sum identity as an actual
universally-quantified real-analysis theorem -- verified independently
via SymPy (`sum(cos(2*pi*g/3 - delta) for g in range(3)) = 0`) before
being written as a Lean proof -- and then the resulting algebra: setting
the empirical Koide ratio `Q = 2/3` forces `ε² = 2`, hence `ε = √2`
(the source's boxed conclusion). The quadratic phase-sum identity
`Σ cos² = 3/2`, which the source uses to derive the `Q`-formula itself,
is not re-derived here; the `Q`-formula is taken as given (as the source
already establishes it) and only the resulting `ε = √2` algebra is
formalized downstream of it.
-/

namespace GppKoide

theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  have h : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_sub, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
  ring

theorem sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  have h : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.sin_sub, Real.cos_pi, Real.sin_pi, Real.sin_pi_div_three]
  ring

theorem cos_four_pi_div_three : Real.cos (4 * Real.pi / 3) = -(1 / 2) := by
  have h : (4 * Real.pi / 3 : ℝ) = Real.pi + Real.pi / 3 := by ring
  rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
  ring

theorem sin_four_pi_div_three : Real.sin (4 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
  have h : (4 * Real.pi / 3 : ℝ) = Real.pi + Real.pi / 3 := by ring
  rw [h, Real.sin_add, Real.cos_pi, Real.sin_pi, Real.sin_pi_div_three]
  ring

/-- The SU(3)_F Weyl-orbit phase sum vanishes for every VEV direction δ:
    `Σ_{g=0}^{2} cos(2πg/3 - δ) = 0`. This is the fact that makes
    `Σ_g √m_g = 3A` in the Koide parametrization. -/
theorem koide_phase_sum_zero (δ : ℝ) :
    Real.cos (-δ) + Real.cos (2 * Real.pi / 3 - δ) + Real.cos (4 * Real.pi / 3 - δ) = 0 := by
  rw [Real.cos_neg, Real.cos_sub, Real.cos_sub, cos_two_pi_div_three, sin_two_pi_div_three,
    cos_four_pi_div_three, sin_four_pi_div_three]
  ring

/-- Setting the empirical Koide ratio `Q = 2/3` in the derived formula
    `Q = (1 + ε²/2)/3` forces `ε² = 2`. -/
theorem koide_epsilon_sq_two (ε : ℝ) (h : (1 + ε ^ 2 / 2) / 3 = 2 / 3) : ε ^ 2 = 2 := by
  linarith

/-- Since the VEV amplitude ε is nonnegative, `ε² = 2` forces `ε = √2`,
    the source's boxed conclusion. -/
theorem koide_epsilon_eq_sqrt_two (ε : ℝ) (hε : 0 ≤ ε) (h : ε ^ 2 = 2) :
    ε = Real.sqrt 2 := by
  rw [← h]
  exact (Real.sqrt_sq hε).symm

end GppKoide
