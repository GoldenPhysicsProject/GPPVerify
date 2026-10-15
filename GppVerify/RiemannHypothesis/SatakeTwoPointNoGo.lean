import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# Nonunitary Satake weights fail the two-point positive-definiteness test

Source: Grok S9/S10, GPP-bridge PR #11; two-point simplification by
Codex/GPT, Oct 14 2026. Finite Gram algebra only, no RH claim.
-/

namespace GppSatakeTwoPointNoGo

open Real

/-- Real symmetric two-point Gram quadratic. -/
def gramEnergy (d c x y : ℝ) : ℝ :=
  d * (x ^ 2 + y ^ 2) + 2 * c * x * y

/-- Antisymmetric eigenvector evaluation. -/
theorem antisymmetric_energy (d c : ℝ) :
    gramEnergy d c 1 (-1) = 2 * (d - c) := by
  unfold gramEnergy
  ring

/-- An off-diagonal exceeding the diagonal obstructs PSD. -/
theorem not_psd_of_off_gt_diag {d c : ℝ} (h : d < c) :
    ¬ (∀ x y : ℝ, 0 ≤ gramEnergy d c x y) := by
  intro hpsd
  have hv := hpsd 1 (-1)
  rw [antisymmetric_energy] at hv
  linarith

/-- Real hyperbolic displacement is non-positive-type at aligned phase. -/
theorem cosh_weight_not_psd {z : ℝ} (hz : z ≠ 0) :
    ¬ (∀ x y : ℝ, 0 ≤ gramEnergy 2 (2 * cosh z) x y) := by
  apply not_psd_of_off_gt_diag
  have hcosh : 1 < cosh z := Real.one_lt_cosh.mpr hz
  linarith

/-- The explicit strictly negative antisymmetric direction. -/
theorem hyperbolic_negative_witness {z : ℝ} (hz : z ≠ 0) :
    gramEnergy 2 (2 * cosh z) 1 (-1) < 0 := by
  rw [antisymmetric_energy]
  have hcosh : 1 < cosh z := Real.one_lt_cosh.mpr hz
  linarith

end GppSatakeTwoPointNoGo
