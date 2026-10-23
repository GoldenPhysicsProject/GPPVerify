import Mathlib.Tactic

/-!
# Constraint-gauged York clock does not fix the geometric size sector

Motivated by Blommaert--Chen, "Time in gravitational subregions and
in closed universes", arXiv:2602.22153 (2026), equations (2.31) and
(2.49), which construct in JT gravity a York-related gravitational
clock with coupled constraint K_grav + K_matter = 0 and a crossed
product observable algebra.

THIS MODULE IS ONLY A FINITE CANONICAL COUNTERMODEL, NOT A
FORMALIZATION OF JT FIELD EQUATIONS OR OF THEIR crossed-product
von Neumann algebra.

A constraint generating translations of an extrinsic-curvature clock
can be gauge redundant while an independent gauge-invariant geometric
size parameter remains variable. Hence establishing a York-related
Hamiltonian constraint by itself does not identify its generator with
the distinct ADM York momentum-shift Y satisfying i_Y Omega = c dV.

This sharpens the precise physical input needed by the volume paper.
-/

namespace GppYorkClockConstraint

structure ClockData where
  clock : ℝ
  gravEnergy : ℝ
  matterModular : ℝ
  size : ℝ

def totalConstraint (z : ClockData) : ℝ :=
  z.gravEnergy + z.matterModular

def clockShift (a : ℝ) (z : ClockData) : ClockData :=
  { z with clock := z.clock + a }

def admissible (z : ClockData) : Prop :=
  totalConstraint z = 0

/-- The clock-gauge translation preserves the coupled gravity/matter
Hamiltonian constraint. -/
theorem clock_shift_preserves_constraint
    (a : ℝ) (z : ClockData) :
    totalConstraint (clockShift a z) = totalConstraint z := by
  rfl

/-- The geometrical size label remains gauge-invariant under
translation of the curvature clock. -/
theorem size_clock_gauge_invariant
    (a : ℝ) (z : ClockData) :
    (clockShift a z).size = z.size := by
  rfl

/-- A coupled York-clock constraint does not imply a fixed numerical
size: explicit constrained states can have different size labels. -/
theorem coupled_clock_constraint_does_not_fix_size :
    ∃ x y : ClockData,
      admissible x ∧ admissible y ∧ x.size ≠ y.size := by
  refine ⟨⟨0, 1, -1, 1⟩, ⟨0, 1, -1, 2⟩, ?_, ?_, ?_⟩
  · norm_num [admissible, totalConstraint]
  · norm_num [admissible, totalConstraint]
  · norm_num

/-- Different sizes cannot lie on the same orbit of pure York-clock
translation, even if both states obey the gravity/matter constraint. -/
theorem different_size_not_clock_gauge_equivalent
    (x y : ClockData) (hsize : x.size ≠ y.size) :
    ¬ ∃ a : ℝ, clockShift a x = y := by
  rintro ⟨a, h⟩
  apply hsize
  have hs : (clockShift a x).size = y.size := congrArg ClockData.size h
  simpa [clockShift] using hs

end GppYorkClockConstraint

#print axioms GppYorkClockConstraint.clock_shift_preserves_constraint
#print axioms GppYorkClockConstraint.size_clock_gauge_invariant
#print axioms GppYorkClockConstraint.coupled_clock_constraint_does_not_fix_size
#print axioms GppYorkClockConstraint.different_size_not_clock_gauge_equivalent
