import Mathlib.Tactic
import GppVerify.StandardModel.FourOrientationGaugeProjection

/-!
# Diagonal gauge averaging and the equal (++/--) representative

If the simultaneous microscopic reversal `D` is a genuine Z2 gauge/deck redundancy, the
canonical finite-group average is

    P_D = (1 + D)/2.

On the four-lift amplitude carrier this projects any vector to the diagonal-even subspace.
In particular a gauge-fixed `|++>` representative is sent to

    (|++> + |-->)/2,

which after normalization has amplitudes `1/sqrt(2)` on the two lifts.  Likewise `|+->`
projects to the equal `|+-> + |-+>` antimatter representative.

Thus the statement "I describe myself as ++, while the gauge-invariant representative is
an equal ++/-- pair" has a precise mathematical realization if, and only if, the diagonal
reversal is truly a redundancy/constraint.  In that case the equal pair is group averaging,
not evidence for two independently observable species.
-/

namespace GppOrientationGaugeAveraging

open GppFourOrientationGaugeProjection

/-- Finite Z2 group average `(v + Dv)/2`, written coordinatewise. -/
def diagAverage (v : Orientation4) : Orientation4 :=
  ((v.1 + v.2.2.2)/2,
   (v.2.1 + v.2.2.1)/2,
   (v.2.2.1 + v.2.1)/2,
   (v.2.2.2 + v.1)/2)

/-- The group average is diagonal-even. -/
theorem diagAverage_even (v : Orientation4) :
    diagReverse (diagAverage v) = diagAverage v := by
  rcases v with ⟨a,b,c,d⟩
  simp [diagAverage, diagReverse]
  ring

/-- Averaging an already-even vector does nothing. -/
theorem diagAverage_fixed_on_even (v : Orientation4)
    (h : diagReverse v = v) :
    diagAverage v = v := by
  obtain ⟨a,b,hv⟩ := diag_even_has_paired_form v h
  rw [hv]
  simp [diagAverage, physicalLift]

/-- Hence the group average is idempotent. -/
theorem diagAverage_idempotent (v : Orientation4) :
    diagAverage (diagAverage v) = diagAverage v := by
  exact diagAverage_fixed_on_even (diagAverage v) (diagAverage_even v)

/-- Four bare kinematic basis lifts. -/
def barePP : Orientation4 := (1,0,0,0)
def barePM : Orientation4 := (0,1,0,0)
def bareMP : Orientation4 := (0,0,1,0)
def bareMM : Orientation4 := (0,0,0,1)

/-- A gauge-fixed `++` or `--` lift projects to the same equal matter pair. -/
theorem average_diagonal_matter_lifts :
    diagAverage barePP = ((1/2:ℂ),0,0,(1/2:ℂ)) ∧
    diagAverage bareMM = ((1/2:ℂ),0,0,(1/2:ℂ)) := by
  constructor <;> norm_num [diagAverage, barePP, bareMM]

/-- The two anti-aligned bare lifts project to the same equal antimatter pair. -/
theorem average_offdiagonal_antimatter_lifts :
    diagAverage barePM = (0,(1/2:ℂ),(1/2:ℂ),0) ∧
    diagAverage bareMP = (0,(1/2:ℂ),(1/2:ℂ),0) := by
  constructor <;> norm_num [diagAverage, barePM, bareMP]

/-- Group averaging preserves the relational charge/matter grading. -/
theorem chi_commutes_diagAverage (v : Orientation4) :
    chi (diagAverage v) = diagAverage (chi v) := by
  rcases v with ⟨a,b,c,d⟩
  simp [diagAverage, chi]
  ring

/-- The averaged `++` representative is proportional to the canonical matter lift. -/
theorem average_pp_eq_half_matterLift :
    diagAverage barePP = ((1/2:ℂ),0,0,(1/2:ℂ)) := by
  exact average_diagonal_matter_lifts.1

end GppOrientationGaugeAveraging
