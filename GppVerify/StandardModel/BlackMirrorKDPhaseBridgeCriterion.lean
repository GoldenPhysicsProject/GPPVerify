import Mathlib.Tactic
import GppVerify.StandardModel.BlackMirrorFoldedCPTOrientation
import GppVerify.StandardModel.FixedCoordinateOppositeQuantumPhase

/-!
# Black-mirror / Kähler--Dirac phase bridge: what is proved and what remains to be identified

Two exact neighboring structures are now available:

1. In the folded black-mirror description, the displayed embedding-time sign is preserved
   when the sheet sign is exchanged; the base radius is also sheet-blind.

2. In the two-sheet Kähler--Dirac interpretation, the two sheets may be assigned opposite
   quantum complex orientations `i <-> -i`, so the microscopic phase generator reverses at
   the SAME coordinate-time increment while its magnitude is unchanged.

The tempting identification is therefore NOT

    black-mirror sheet flip = coordinate t -> -t,

which is false in the folded description.  The mathematically viable target is

    black-mirror sheet flip  --->  quantum complex orientation i -> -i.

If that geometric/fermionic dictionary is established for the actual Dirac/KD bundle on the
black-mirror spacetime, then the sheet exchange can reverse microscopic phase orientation
without reversing the common displayed time coordinate.  This file packages only the
already-proved algebraic consequence; it does not assert that the bundle intertwiner exists.
-/

namespace GppBlackMirrorKDPhaseBridgeCriterion

open GppBlackMirrorFoldedCPTOrientation
open GppFixedCoordinateOppositeQuantumPhase

/-- A minimal dictionary hypothesis: a geometric sheet flip is represented on the quantum
    phase carrier by reversal of the complex phase generator. -/
def SheetToPhaseDictionary (omega : ℝ) : Prop :=
  minusPhaseGenerator omega = - plusPhaseGenerator omega

/-- The candidate dictionary holds algebraically for the KD `i <-> -i` phase carriers. -/
theorem kd_phase_dictionary_algebra (omega : ℝ) : SheetToPhaseDictionary omega := by
  exact opposite_i_flips_phase_generator omega

/-- Under the dictionary, one fixed coordinate-time increment carries opposite microscopic
    phase increments on the two sheets. -/
theorem fixed_time_sheet_phase_flip (omega dt : ℝ)
    (_h : SheetToPhaseDictionary omega) :
    phaseIncrement (minusPhaseGenerator omega) dt =
      - phaseIncrement (plusPhaseGenerator omega) dt := by
  exact same_dt_opposite_phase_increment omega dt

/-- At the same time, the microscopic frequency magnitude is identical. -/
theorem sheet_phase_magnitude_equal (omega : ℝ) :
    phaseMagnitudeSq (plusPhaseGenerator omega) =
      phaseMagnitudeSq (minusPhaseGenerator omega) := by
  exact both_orientations_same_frequency_magnitude omega

/-- Black-mirror folded geometry itself preserves the displayed embedding-time sign. -/
theorem black_mirror_sheet_not_coordinate_time_reversal (x : FoldSigns) :
    (foldedCPTSigns x).1 = x.1 :=
  foldedCPT_preserves_embedding_time x

/-- Capstone target: the consistent combined reading is "same displayed coordinate time,
    opposite microscopic quantum phase orientation", not literal backward coordinate-time
    propagation on the folded diagram. -/
theorem same_time_opposite_phase_capstone
    (x : FoldSigns) (omega dt : ℝ) :
    (foldedCPTSigns x).1 = x.1 ∧
    phaseIncrement (minusPhaseGenerator omega) dt =
      - phaseIncrement (plusPhaseGenerator omega) dt ∧
    phaseMagnitudeSq (plusPhaseGenerator omega) =
      phaseMagnitudeSq (minusPhaseGenerator omega) := by
  exact ⟨foldedCPT_preserves_embedding_time x,
    same_dt_opposite_phase_increment omega dt,
    both_orientations_same_frequency_magnitude omega⟩

end GppBlackMirrorKDPhaseBridgeCriterion
