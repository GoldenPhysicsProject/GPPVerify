import Mathlib.Tactic
import GppVerify.RiemannHypothesis.OrientationCriticalRealStructureBridge

/-!
# Arrow dictionary: exact finite algebra behind the RH orientation picture

This file formalizes the pieces of the October 2026 Arrow Dictionary that are
honest finite algebra:

* the centered orientation bias changes sign under s ↦ 1 - conj s;
* the average bias on every two-point reversal orbit is therefore zero
  unconditionally;
* zero individual bias is equivalent to being fixed by the reversal, hence to
  Re s = 1/2;
* the two-point swap carries an indefinite (+,-) block;
* conjugating an operator by an invertible linear gauge preserves its
  eigenvalue/eigencharacter.

No positivity theorem for the arithmetic Weil form is assumed or proved here.
-/

namespace GppRHArrowDictionary

open Complex
open GppOrientationCriticalRealStructureBridge

/-- Arithmetic complete reversal in the original s coordinate. -/
def reversal (s : ℂ) : ℂ := 1 - starRingEnd ℂ s

/-- Signed displacement from the critical line. -/
def orientationBias (s : ℂ) : ℝ := s.re - (1 / 2 : ℝ)

/-- Complete reversal changes the sign of the centered orientation bias. -/
theorem orientationBias_reversal (s : ℂ) :
    orientationBias (reversal s) = - orientationBias s := by
  simp [orientationBias, reversal]
  ring

/-- Every two-point reversal orbit has exactly zero average orientation bias.
    This is unconditional and therefore strictly weaker than RH. -/
theorem reversal_orbit_bias_sum_zero (s : ℂ) :
    orientationBias s + orientationBias (reversal s) = 0 := by
  rw [orientationBias_reversal]
  ring

/-- Individual zero bias is exactly the critical-line condition. -/
theorem orientationBias_eq_zero_iff (s : ℂ) :
    orientationBias s = 0 ↔ s.re = (1 / 2 : ℝ) := by
  constructor <;> intro h <;> simp [orientationBias] at h ⊢ <;> linarith

/-- Individual zero bias is exactly the fixed-point condition for complete reversal. -/
theorem orientationBias_eq_zero_iff_fixed (s : ℂ) :
    orientationBias s = 0 ↔ reversal s = s := by
  rw [orientationBias_eq_zero_iff]
  simpa [reversal] using (s_fixed_iff_critical s).symm

/-- The finite two-point D-twisted block.  In coordinates this is the
    quadratic form of the swap matrix sigma_1. -/
def swapTwistedForm (v : ℝ × ℝ) : ℝ :=
  v.1 * v.2 + v.2 * v.1

/-- The coherent direction is positive. -/
theorem swapTwistedForm_coherent (a : ℝ) :
    swapTwistedForm (a, a) = 2 * a^2 := by
  simp [swapTwistedForm]
  ring

/-- The anti-coherent direction is negative. -/
theorem swapTwistedForm_antiCoherent (a : ℝ) :
    swapTwistedForm (a, -a) = -2 * a^2 := by
  simp [swapTwistedForm]
  ring

/-- A nonzero two-point swap block is indefinite: it has an explicit positive
    and an explicit negative vector. -/
theorem swapTwistedForm_indefinite :
    0 < swapTwistedForm ((1 : ℝ), 1) ∧
    swapTwistedForm ((1 : ℝ), -1) < 0 := by
  constructor <;> norm_num [swapTwistedForm]

section Gauge

variable {𝕜 V : Type*}
variable [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Conjugation of a linear operator by an invertible linear gauge. -/
def gaugeConjugate (M : V ≃ₗ[𝕜] V) (T : V →ₗ[𝕜] V) : V →ₗ[𝕜] V :=
  M.toLinearMap.comp (T.comp M.symm.toLinearMap)

/-- Lemma G: an invertible gauge conjugation preserves every eigencharacter.
    It can change normalization/where the unitary axis is written, but it cannot
    move an eigenvalue. -/
theorem gaugeConjugate_preserves_eigencharacter
    (M : V ≃ₗ[𝕜] V) (T : V →ₗ[𝕜] V) (v : V) (c : 𝕜)
    (h : T v = c • v) :
    gaugeConjugate M T (M v) = c • M v := by
  simp [gaugeConjugate, h]

end Gauge

end GppRHArrowDictionary

#print axioms GppRHArrowDictionary.orientationBias_reversal
#print axioms GppRHArrowDictionary.reversal_orbit_bias_sum_zero
#print axioms GppRHArrowDictionary.orientationBias_eq_zero_iff_fixed
#print axioms GppRHArrowDictionary.swapTwistedForm_indefinite
#print axioms GppRHArrowDictionary.gaugeConjugate_preserves_eigencharacter
