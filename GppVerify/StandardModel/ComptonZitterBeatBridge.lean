import Mathlib.Tactic
import GppVerify.StandardModel.OrientationMassTime

/-!
# Compton phase, positive/negative energy splitting, and the zitter beat frequency

For a rest-frame Dirac mode the two energy signs are

    E_+ = + m c^2,
    E_- = - m c^2.

Dividing by hbar gives the two phase angular velocities

    omega_+ = + m c^2 / hbar,
    omega_- = - m c^2 / hbar.

Their relative phase therefore rotates at

    omega_+ - omega_- = 2 m c^2 / hbar = 2 omega_C.

This is the exact algebraic origin of the standard zitterbewegung factor of two.  It is a
beat/relative-phase statement between positive- and negative-energy sectors; no claim is
made here that a particle literally traverses a second spacetime or crosses a cosmological
boundary.
-/

namespace GppComptonZitterBeatBridge

open GppOrientationMassTime

/-- Positive rest-energy phase rate. -/
def positiveRestPhaseRate (m c hbar : ℝ) : ℝ := m * c^2 / hbar

/-- Negative rest-energy phase rate. -/
def negativeRestPhaseRate (m c hbar : ℝ) : ℝ := -(m * c^2 / hbar)

/-- Relative phase/beat rate between the two rest-energy signs. -/
def restBeatRate (m c hbar : ℝ) : ℝ :=
  positiveRestPhaseRate m c hbar - negativeRestPhaseRate m c hbar

/-- The positive rest phase rate is exactly the reduced Compton angular frequency. -/
theorem positiveRestPhaseRate_eq_comptonFrequency (m c hbar : ℝ) :
    positiveRestPhaseRate m c hbar = comptonFrequency m c hbar := by
  rfl

/-- The negative branch carries the opposite Compton phase orientation. -/
theorem negativeRestPhaseRate_eq_neg_comptonFrequency (m c hbar : ℝ) :
    negativeRestPhaseRate m c hbar = - comptonFrequency m c hbar := by
  rfl

/-- Exact beat identity: the positive/negative relative phase runs at twice the Compton
frequency. -/
theorem restBeatRate_eq_two_comptonFrequency (m c hbar : ℝ) :
    restBeatRate m c hbar = 2 * comptonFrequency m c hbar := by
  simp [restBeatRate, positiveRestPhaseRate, negativeRestPhaseRate, comptonFrequency]
  ring

/-- Hence the beat rate is exactly the project's zitter frequency. -/
theorem restBeatRate_eq_zitterFrequency (m c hbar : ℝ) :
    restBeatRate m c hbar = zitterFrequency m c hbar := by
  rw [restBeatRate_eq_two_comptonFrequency]
  rfl

/-- The half-frequency relation is exact whenever `2` is invertible, independently of
mass normalization. -/
theorem comptonFrequency_eq_half_restBeatRate (m c hbar : ℝ) :
    comptonFrequency m c hbar = restBeatRate m c hbar / 2 := by
  rw [restBeatRate_eq_two_comptonFrequency]
  ring

end GppComptonZitterBeatBridge
