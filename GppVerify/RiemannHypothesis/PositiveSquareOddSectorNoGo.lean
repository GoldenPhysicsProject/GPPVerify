import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Positive energy plus an orientation grading does not remove the odd sector

The arithmetic Hodge/OS programme needs more than a positive ambient Hilbert metric and a
first-order operator whose square is positive.  A nonzero odd/ghost sector can coexist with
all of that structure.

This file gives the smallest exact model.  Let

    gamma = sigma3,     D = sigma1.

Then `gamma^2=1`, `D^2=1`, and `gamma D = -D gamma`.  Thus `D^2` is positive/even, but the
`gamma=-1` eigenspace is visibly nonzero.  Therefore the spin/metaplectic algebra

    grading + reflection-odd first-order generator + positive square

does not by itself prove the arithmetic no-ghost statement required for RH.  One still
needs the genuinely arithmetic theorem that the completed physical cohomology has no odd
part (equivalently, the relevant Weil/OS Gram form is positive).
-/

namespace GppPositiveSquareOddSectorNoGo

/-- Z2 grading. -/
def grading : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1,0;
     0,-1]

/-- Odd first-order operator. -/
def oddDirac : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0,1;
     1,0]

/-- Canonical nonzero odd vector. -/
def oddVector : Fin 2 → ℝ := ![0,1]

/-- The grading is an involution. -/
theorem grading_sq_one : grading * grading = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [grading, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- The first-order operator has positive square `1`. -/
theorem oddDirac_sq_one : oddDirac * oddDirac = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [oddDirac, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- The grading anticommutes with the first-order operator. -/
theorem grading_anticommutes_oddDirac :
    grading * oddDirac = -(oddDirac * grading) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [grading, oddDirac, Matrix.mul_apply, Fin.sum_univ_two]

/-- The odd vector is genuinely nonzero. -/
theorem oddVector_ne_zero : oddVector ≠ 0 := by
  intro h
  have h1 := congrFun h (1 : Fin 2)
  norm_num [oddVector] at h1

/-- The nonzero vector lies in the `-1` grading sector. -/
theorem grading_oddVector : grading *ᵥ oddVector = -oddVector := by
  ext i
  fin_cases i <;>
    norm_num [grading, oddVector, Matrix.mulVec, Fin.sum_univ_two]

/-- Capstone no-go: all positive-square/even-grading algebra holds while a nonzero odd
state still exists. -/
theorem positive_square_does_not_kill_odd_sector :
    grading * grading = (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    oddDirac * oddDirac = (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    grading * oddDirac = -(oddDirac * grading) ∧
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ grading *ᵥ v = -v := by
  refine ⟨grading_sq_one, oddDirac_sq_one, grading_anticommutes_oddDirac, ?_⟩
  exact ⟨oddVector, oddVector_ne_zero, grading_oddVector⟩

end GppPositiveSquareOddSectorNoGo
