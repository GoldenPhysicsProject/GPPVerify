import GppVerify.CelestialHolography.ConformalShadowPrincipalSeries
import GppVerify.RiemannHypothesis.ScaleMassDiagnostic
import Mathlib.Tactic

/-!
# Shadow-KMS norm rigidity

The anti-linear arithmetic shadow s |-> 1-conj(s) reverses the real
half-density displacement from Re(s)=1/2 while preserving the spectral
frequency. Consequently its normalized dilation-character norm is reciprocal
to the original one.

If a physical shadow/CPT implementation preserves that norm at even one
nontrivial positive scale, the parameter is forced onto the principal series.

This is an abstract representation-theoretic criterion only. It does not prove
that zeta zeros satisfy the required physical shadow-isometry hypothesis.
-/

namespace GppShadowKMSRigidity

open Complex
open GppScaleMass
open GppConformalShadowPrincipalSeries

/-- The anti-linear arithmetic shadow flips the centered real displacement. -/
theorem antiLinearShadow_centered_re (s : ℂ) :
    (antiLinearShadow 1 s).re - (1 : ℝ) / 2 =
      -(s.re - (1 : ℝ) / 2) := by
  simp [antiLinearShadow]
  ring

/-- The dilation-character norms of a parameter and its anti-linear shadow
are exact reciprocals. -/
theorem dilation_norm_shadow_product_one
    (s : ℂ) (a : ℝ) :
    ‖dilationCharacter s a‖ *
      ‖dilationCharacter (antiLinearShadow 1 s) a‖ = 1 := by
  rw [norm_dilationCharacter, norm_dilationCharacter]
  rw [antiLinearShadow_centered_re]
  rw [← Real.exp_add]
  convert Real.exp_zero using 2
  ring

/--
A single nontrivial positive scale is enough: if anti-linear shadow preserves
the norm of the half-density dilation character, then Re(s)=1/2.
-/
theorem principal_of_shadow_norm_eq
    {s : ℂ} {a : ℝ}
    (ha : 0 < a) (ha1 : a ≠ 1)
    (hiso :
      ‖dilationCharacter s a‖ =
        ‖dilationCharacter (antiLinearShadow 1 s) a‖) :
    s.re = (1 : ℝ) / 2 := by
  rw [norm_dilationCharacter, norm_dilationCharacter] at hiso
  rw [antiLinearShadow_centered_re] at hiso
  have hexp :
      Real.log a * (s.re - (1 : ℝ) / 2) =
        -(Real.log a * (s.re - (1 : ℝ) / 2)) := by
    rw [← mul_neg]
    exact Real.exp_injective hiso
  have hloga : Real.log a ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one ha ha1
  have hprod : Real.log a * (s.re - (1 : ℝ) / 2) = 0 := by
    linarith
  have hcenter : s.re - (1 : ℝ) / 2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hloga
  linarith

/-- On the principal series the shadow norm equality holds at every scale. -/
theorem shadow_norm_eq_of_principal
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2) (a : ℝ) :
    ‖dilationCharacter s a‖ =
      ‖dilationCharacter (antiLinearShadow 1 s) a‖ := by
  rw [critical_line_dilation_unitary hs a]
  have hshadow : (antiLinearShadow 1 s).re = (1 : ℝ) / 2 := by
    simp [antiLinearShadow, hs]
    norm_num
  rw [critical_line_dilation_unitary hshadow a]

/-- Exact one-scale characterization by anti-linear shadow isometry. -/
theorem principal_iff_shadow_norm_eq
    {s : ℂ} {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) :
    s.re = (1 : ℝ) / 2 ↔
      ‖dilationCharacter s a‖ =
        ‖dilationCharacter (antiLinearShadow 1 s) a‖ := by
  constructor
  · intro hs
    exact shadow_norm_eq_of_principal hs a
  · intro h
    exact principal_of_shadow_norm_eq ha ha1 h

end GppShadowKMSRigidity

#print axioms GppShadowKMSRigidity.antiLinearShadow_centered_re
#print axioms GppShadowKMSRigidity.dilation_norm_shadow_product_one
#print axioms GppShadowKMSRigidity.principal_of_shadow_norm_eq
#print axioms GppShadowKMSRigidity.principal_iff_shadow_norm_eq
