import GppVerify.CelestialHolography.CelestialShadowHelicity
import GppVerify.CelestialHolography.DiscreteSymmetryHelicity
import Mathlib.Tactic

/-!
# Celestial shadow is not pure time reversal on nonzero helicity

The representation-theoretic shadow sends the celestial spin label `J` to `-J`.
For a massless state, ordinary time reversal reverses both angular momentum and
momentum and therefore preserves helicity, while parity reverses helicity.

This file records the exact algebraic separation.  It does not identify shadow
with parity, PT, or CPT as a full operator on the physical Hilbert space; it only
proves the necessary helicity-sign constraint that any such identification must
satisfy.
-/

namespace GppShadowDiscreteSymmetrySeparation

/-- Shadow action on a real helicity label. -/
def shadowHelicity (h : ℝ) : ℝ := -h

/-- Pure time reversal preserves the helicity label. -/
def timeReversalHelicity (h : ℝ) : ℝ := h

/-- Parity reverses the helicity label. -/
def parityHelicity (h : ℝ) : ℝ := -h

/-- Shadow and parity have the same necessary action on helicity labels. -/
theorem shadowHelicity_eq_parityHelicity (h : ℝ) :
    shadowHelicity h = parityHelicity h := rfl

/-- On every nonzero-helicity sector, celestial shadow cannot have the same
helicity action as pure time reversal. -/
theorem shadowHelicity_ne_timeReversalHelicity
    {h : ℝ} (hh : h ≠ 0) :
    shadowHelicity h ≠ timeReversalHelicity h := by
  exact GppDiscreteSymmetryHelicity.nonzero_flip_ne_preserve hh

/-- The spin-two sector gives the concrete graviton separation. -/
theorem graviton_shadow_ne_time_reversal :
    shadowHelicity 2 ≠ timeReversalHelicity 2 := by
  norm_num [shadowHelicity, timeReversalHelicity]

/-- The spin-one sector gives the corresponding gauge-boson separation. -/
theorem gauge_shadow_ne_time_reversal :
    shadowHelicity 1 ≠ timeReversalHelicity 1 := by
  norm_num [shadowHelicity, timeReversalHelicity]

end GppShadowDiscreteSymmetrySeparation

#print axioms GppShadowDiscreteSymmetrySeparation.shadowHelicity_eq_parityHelicity
#print axioms GppShadowDiscreteSymmetrySeparation.shadowHelicity_ne_timeReversalHelicity
#print axioms GppShadowDiscreteSymmetrySeparation.graviton_shadow_ne_time_reversal
