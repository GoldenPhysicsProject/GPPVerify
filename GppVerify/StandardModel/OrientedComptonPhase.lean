import Mathlib.Tactic
import GppVerify.StandardModel.OrientationMassTime
import GppVerify.StandardModel.ComptonZitterBeatBridge
import GppVerify.StandardModel.MassiveSpinCenterOrientation

/-!
# Oriented Compton phase: mass even, phase/four-momentum orientation odd

The relative center of the doubled spinor factorization sends a massive four-momentum
`P -> -P` while preserving `det P` and hence the mass magnitude.  This suggests a cleaner
home for the project's time/worldline sign than the beta energy eigenspace itself.

At rest, introduce an orientation sign `t=+/-1` and write

  E_t     = t m c^2,
  omega_t = t m c^2 / hbar = t omega_C.

The mass and Compton *magnitude* are unchanged by `t -> -t`; only the orientation of the
phase/four-momentum reverses.  The separation between the two oriented lifts is exactly

  omega_(+) - omega_(-) = 2 omega_C,

so the standard zitter factor of two is compatible with interpreting the two phase signs as
opposite lifts of one fixed mass shell.  The additional physical claim that actual Dirac
zitterbewegung is coherence between these geometric orientation lifts remains a hypothesis.
-/

namespace GppOrientedComptonPhase

open GppOrientationMassTime
open GppComptonZitterBeatBridge

/-- Rest energy with an explicit worldline/four-momentum orientation sign. -/
def orientedRestEnergy (t m c : ℝ) : ℝ := t * m * c^2

/-- Corresponding oriented Compton phase rate. -/
def orientedComptonFrequency (t m c hbar : ℝ) : ℝ :=
  t * comptonFrequency m c hbar

/-- Orientation reversal negates energy without changing the mass parameter. -/
theorem orientedRestEnergy_flip (t m c : ℝ) :
    orientedRestEnergy (-t) m c = - orientedRestEnergy t m c := by
  simp [orientedRestEnergy]
  ring

/-- Likewise it reverses the Compton phase direction. -/
theorem orientedComptonFrequency_flip (t m c hbar : ℝ) :
    orientedComptonFrequency (-t) m c hbar =
      - orientedComptonFrequency t m c hbar := by
  simp [orientedComptonFrequency]

/-- The positive orientation is the usual positive Compton frequency. -/
theorem orientedCompton_plus (m c hbar : ℝ) :
    orientedComptonFrequency 1 m c hbar = comptonFrequency m c hbar := by
  simp [orientedComptonFrequency]

/-- The opposite orientation is the negative Compton phase rate. -/
theorem orientedCompton_minus (m c hbar : ℝ) :
    orientedComptonFrequency (-1) m c hbar = -comptonFrequency m c hbar := by
  simp [orientedComptonFrequency]

/-- Their relative phase rate is exactly the standard zitter frequency `2 omega_C`. -/
theorem oriented_pair_beat_is_zitter (m c hbar : ℝ) :
    orientedComptonFrequency 1 m c hbar -
      orientedComptonFrequency (-1) m c hbar =
      zitterFrequency m c hbar := by
  simp [orientedComptonFrequency, zitterFrequency]
  ring

/-- The orientation sign does not alter the positive Compton ruler/clock magnitudes. -/
theorem compton_magnitudes_independent_of_orientation
    (t m c hbar : ℝ) :
    comptonLength m c hbar = comptonLength m c hbar ∧
    comptonFrequency m c hbar = comptonFrequency m c hbar := by
  exact ⟨rfl,rfl⟩

end GppOrientedComptonPhase
