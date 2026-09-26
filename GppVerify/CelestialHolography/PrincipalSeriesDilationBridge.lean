import GppVerify.CelestialHolography.PositiveRealPrincipalSeries
import GppVerify.RiemannHypothesis.ScaleMassDiagnostic

/-!
# Principal-series / dilation-unitarity bridge

This module closes the exact algebraic equivalence between the celestial principal axis
`Re Δ = 1` under `Δ = 2s` and unit modulus of the half-density-normalized multiplicative
dilation character at any fixed nontrivial positive scale.

For scales `a > 1`, it also classifies the two off-axis regions: `Re Δ > 1` gives
strict amplification and `Re Δ < 1` gives strict contraction.
-/

namespace GppPrincipalSeriesDilationBridge

open GppPositiveReal
open GppScaleMass

/-- For every fixed positive scale `a ≠ 1`, celestial principal-series kinematics and
half-density dilation unitarity are exactly equivalent. -/
theorem celestial_principal_iff_dilation_unitary
    {s : ℂ} {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) :
    (celestialWeight s).re = 1 ↔ ‖dilationCharacter s a‖ = 1 := by
  rw [celestialWeight_re_eq_one_iff]
  exact critical_line_iff_dilation_unitary ha ha1

/-- The same equivalence stated in three-way form: the arithmetic critical axis,
the celestial principal axis, and multiplicative dilation unitarity coincide. -/
theorem critical_celestial_dilation_equiv
    {s : ℂ} {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) :
    (s.re = (1 : ℝ) / 2 ↔ (celestialWeight s).re = 1) ∧
    ((celestialWeight s).re = 1 ↔ ‖dilationCharacter s a‖ = 1) := by
  constructor
  · exact celestialWeight_re_eq_one_iff.symm
  · exact celestial_principal_iff_dilation_unitary ha ha1

/-- At any dilation scale `a > 1`, the celestial supercritical half-plane
`Re Δ > 1` is strictly amplifying. -/
theorem celestial_supercritical_dilation_expands
    {s : ℂ} {a : ℝ} (ha : 1 < a) (hΔ : 1 < (celestialWeight s).re) :
    1 < ‖dilationCharacter s a‖ := by
  have hs : (1 : ℝ) / 2 < s.re := by
    simp [celestialWeight] at hΔ
    linarith
  rw [norm_dilationCharacter, one_lt_exp_iff]
  exact mul_pos (Real.log_pos ha) (sub_pos.mpr hs)

/-- At any dilation scale `a > 1`, the celestial subcritical half-plane
`Re Δ < 1` is strictly contractive. -/
theorem celestial_subcritical_dilation_contracts
    {s : ℂ} {a : ℝ} (ha : 1 < a) (hΔ : (celestialWeight s).re < 1) :
    ‖dilationCharacter s a‖ < 1 := by
  have hs : s.re < (1 : ℝ) / 2 := by
    simp [celestialWeight] at hΔ
    linarith
  rw [norm_dilationCharacter, Real.exp_lt_one_iff]
  exact mul_neg_of_pos_of_neg (Real.log_pos ha) (sub_neg.mpr hs)

end GppPrincipalSeriesDilationBridge

#print axioms GppPrincipalSeriesDilationBridge.celestial_principal_iff_dilation_unitary
#print axioms GppPrincipalSeriesDilationBridge.critical_celestial_dilation_equiv
#print axioms GppPrincipalSeriesDilationBridge.celestial_supercritical_dilation_expands
#print axioms GppPrincipalSeriesDilationBridge.celestial_subcritical_dilation_contracts
