import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-!
# Shadow kernel Gamma-function ratio for dark matter abundance

Source: ONON5213.tex, "The Grassmannian Spinor Bundle: Time Reversal,
Chirality, and Dark Matter" chapter. The dark matter abundance formula
`Ω_DM/Ω_b = 1 + N(1/2)/N(3/2) + O(m_ν) = 5.03` uses the shadow kernel
normalization ratio `N(1/2)/N(3/2) = Γ(1/2)²/Γ(3/2)² = 4`.

This file formalizes that Gamma-function ratio as an actual real-analysis
theorem, using Mathlib's Gamma function and its functional equation --
verified independently via SymPy (`gamma(1/2)**2/gamma(3/2)**2 = 4`)
before being written as a Lean proof. The remaining physical content --
deriving `N(Δ)` from the shadow kernel itself, and the `O(m_ν)`
mirror-neutrino correction -- is genuinely deep cosmological modeling
and is not attempted here.
-/

namespace GppDMGamma

/-- Γ(3/2) = (1/2)·Γ(1/2), from the Gamma function's functional equation
    Γ(s+1) = s·Γ(s) at s = 1/2. -/
theorem gamma_three_half_eq : Real.Gamma (3 / 2 : ℝ) = (1 / 2) * Real.Gamma (1 / 2) := by
  have h : (3 : ℝ) / 2 = 1 / 2 + 1 := by norm_num
  rw [h]
  exact Real.Gamma_add_one (by norm_num)

/-- The shadow kernel normalization ratio Γ(1/2)²/Γ(3/2)² = 4. -/
theorem gamma_ratio_one_half_three_half :
    Real.Gamma (1 / 2 : ℝ) ^ 2 / Real.Gamma (3 / 2 : ℝ) ^ 2 = 4 := by
  have hpos : (0 : ℝ) < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  rw [gamma_three_half_eq]
  have hne : Real.Gamma (1 / 2 : ℝ) ≠ 0 := ne_of_gt hpos
  field_simp
  try ring

/-- The dark-matter-to-baryon ratio's leading term:
    1 + Γ(1/2)²/Γ(3/2)² = 5, matching "the factor of 5 derived from
    Gamma functions with no free parameters" -- before the O(m_ν)
    mirror-neutrino correction that brings it to the quoted 5.03. -/
theorem dm_baryon_leading_term :
    1 + Real.Gamma (1 / 2 : ℝ) ^ 2 / Real.Gamma (3 / 2 : ℝ) ^ 2 = 5 := by
  rw [gamma_ratio_one_half_three_half]
  norm_num

/-- The shadow kernel normalization N(Δ) = Γ(Δ)/(π·Γ(2-Δ)) at Δ = 3/2
    (source: ONON5213.tex, Dark Matter chapter, Theorem "Shadow Kernel
    at Δ = 3/2"): N(3/2) = 1/(2π), the exact normalization of the
    hidden-sector shadow kernel `K_{3/2}(z,w) = N(3/2)/|z-w|`. -/
theorem shadow_kernel_normalization_three_half :
    Real.Gamma (3 / 2 : ℝ) / (Real.pi * Real.Gamma (2 - 3 / 2 : ℝ)) = 1 / (2 * Real.pi) := by
  have h1 : (2 - 3 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [h1, gamma_three_half_eq]
  have hpos : (0 : ℝ) < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have hne : Real.Gamma (1 / 2 : ℝ) ≠ 0 := ne_of_gt hpos
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  try ring

end GppDMGamma
