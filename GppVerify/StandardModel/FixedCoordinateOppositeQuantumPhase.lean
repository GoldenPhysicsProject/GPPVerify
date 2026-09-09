import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

/-!
# Fixed coordinate time, opposite quantum phase orientation

Boyle--Deng's two-sheet Kähler--Dirac interpretation states that the two sheets may be viewed
as using opposite square roots of -1: `+i` on one sheet and `-i` on the other.  Accordingly,
a plane wave `exp(-i p.x)` on one sheet corresponds to `exp(+i p.x)` on the other, while
both sheets are quantized with positive energy and positive norm in their own convention.

The important conceptual point is that reversing the quantum complex orientation does NOT
require reversing the coordinate value `t`.  At fixed real coordinate time and fixed
positive frequency magnitude omega, the infinitesimal phase generator

    g_+(omega) = - i omega

is replaced by

    g_-(omega) = + i omega = -g_+(omega).

Thus a microscopic phase/frequency arrow can reverse while the displayed spacetime time
coordinate still increases in the same direction.  This is the exact elementary algebra
behind the project's distinction between the time dimension and the microscopic temporal
phase orientation.  Entropy/thermodynamic time does not enter this theorem.
-/

namespace GppFixedCoordinateOppositeQuantumPhase

open scoped ComplexConjugate

/-- Positive-sheet infinitesimal phase generator for frequency magnitude omega. -/
def plusPhaseGenerator (omega : ℝ) : ℂ := -Complex.I * (omega : ℂ)

/-- Opposite-complex-structure sheet generator at the SAME coordinate time. -/
def minusPhaseGenerator (omega : ℝ) : ℂ := Complex.I * (omega : ℂ)

/-- Reversing the quantum complex orientation reverses the phase generator. -/
theorem opposite_i_flips_phase_generator (omega : ℝ) :
    minusPhaseGenerator omega = - plusPhaseGenerator omega := by
  simp [minusPhaseGenerator, plusPhaseGenerator]

/-- Complex conjugation implements the same phase-orientation flip for real omega. -/
theorem conjugation_flips_phase_generator (omega : ℝ) :
    conj (plusPhaseGenerator omega) = minusPhaseGenerator omega := by
  simp [plusPhaseGenerator, minusPhaseGenerator]

/-- The squared frequency magnitude is independent of the phase orientation. -/
def phaseMagnitudeSq (g : ℂ) : ℝ := Complex.normSq g

 theorem both_orientations_same_frequency_magnitude (omega : ℝ) :
    phaseMagnitudeSq (plusPhaseGenerator omega) =
      phaseMagnitudeSq (minusPhaseGenerator omega) := by
  simp [phaseMagnitudeSq, plusPhaseGenerator, minusPhaseGenerator]

/-- Both generators have norm-squared omega^2. -/
theorem phaseMagnitudeSq_eq_omega_sq (omega : ℝ) :
    phaseMagnitudeSq (plusPhaseGenerator omega) = omega^2 ∧
    phaseMagnitudeSq (minusPhaseGenerator omega) = omega^2 := by
  constructor <;>
    simp [phaseMagnitudeSq, plusPhaseGenerator, minusPhaseGenerator,
      Complex.normSq_apply] <;> ring

/-- Fixed-coordinate-time evolution uses the same real elapsed time on both sheets; only the
    complex phase orientation changes.  This finite statement avoids conflating `t -> -t`
    with `i -> -i`. -/
def phaseIncrement (g : ℂ) (dt : ℝ) : ℂ := (dt : ℂ) * g

 theorem same_dt_opposite_phase_increment (omega dt : ℝ) :
    phaseIncrement (minusPhaseGenerator omega) dt =
      - phaseIncrement (plusPhaseGenerator omega) dt := by
  simp [phaseIncrement, opposite_i_flips_phase_generator]
  ring

/-- Capstone: at one and the same coordinate-time increment, opposite quantum complex
    orientations yield opposite microscopic phase increments with identical magnitude. -/
theorem fixed_coordinate_phase_orientation_capstone (omega dt : ℝ) :
    phaseIncrement (minusPhaseGenerator omega) dt =
      - phaseIncrement (plusPhaseGenerator omega) dt ∧
    phaseMagnitudeSq (plusPhaseGenerator omega) =
      phaseMagnitudeSq (minusPhaseGenerator omega) := by
  exact ⟨same_dt_opposite_phase_increment omega dt,
    both_orientations_same_frequency_magnitude omega⟩

end GppFixedCoordinateOppositeQuantumPhase
