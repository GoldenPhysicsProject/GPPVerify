import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic

/-!
# Two complex structures and a microscopic temporal-orientation grading

This module isolates the algebra suggested by the project's charge/time-orientation
programme without identifying the microscopic sign with the thermodynamic arrow.

Let `I` and `J` be two commuting complex structures on the same finite-dimensional
complex carrier:

    I^2 = -1,
    J^2 = -1,
    I J = J I.

The intended physics dictionary to be tested later is:

* `I`: internal/gauge phase orientation (or the representation-theoretic complex
  structure whose sign distinguishes a representation from its conjugate);
* `J`: microscopic temporal/frequency complex structure, i.e. the choice of phase
  winding / positive-frequency orientation on the one-particle solution space.

These are deliberately distinct from the macroscopic thermodynamic arrow, which is a
coarse-grained property of many-body states and boundary conditions and is not encoded
here.

Define the relative involution

    K = - I J.

Because the two quarter-turns commute, `K^2 = +1`.  Simultaneously reversing both
complex orientations leaves `K` unchanged, whereas reversing exactly one flips `K`.
Thus a binary relational character can arise from two underlying orientation structures:

    (I,J) ~ (-I,-J),
    K(I,-J) = -K(I,J),
    K(-I,J) = -K(I,J).

This is the abstract algebraic form of the proposed `q*t` relation.  The theorem does not
assert that electric charge is literally a matrix complex structure, nor that `J` is Wigner
T or the entropy arrow.  Those are separate representation-theoretic and dynamical
questions.
-/

namespace GppTwoComplexStructureTemporalOrientation

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev EndC := Matrix n n ℂ

/-- Relative `Z2` grading carried by two commuting complex structures. -/
def relativeOrientation (I J : EndC) : EndC := -(I * J)

/-- The product of two commuting complex structures is an involution. -/
theorem relativeOrientation_sq_one
    (I J : EndC)
    (hI : I * I = -(1 : EndC))
    (hJ : J * J = -(1 : EndC))
    (hcomm : I * J = J * I) :
    relativeOrientation I J * relativeOrientation I J = (1 : EndC) := by
  unfold relativeOrientation
  calc
    (-(I * J)) * (-(I * J)) = (I * J) * (I * J) := by simp
    _ = I * (J * I) * J := by simp [Matrix.mul_assoc]
    _ = I * (I * J) * J := by rw [← hcomm]
    _ = (I * I) * (J * J) := by simp [Matrix.mul_assoc]
    _ = (-(1 : EndC)) * (-(1 : EndC)) := by rw [hI, hJ]
    _ = (1 : EndC) := by simp

/-- Reversing both microscopic complex orientations leaves the relative grading fixed. -/
theorem reverse_both_preserves_relativeOrientation (I J : EndC) :
    relativeOrientation (-I) (-J) = relativeOrientation I J := by
  simp [relativeOrientation]

/-- Reversing only the first orientation flips the relative grading. -/
theorem reverse_first_flips_relativeOrientation (I J : EndC) :
    relativeOrientation (-I) J = - relativeOrientation I J := by
  simp [relativeOrientation]

/-- Reversing only the second orientation flips the relative grading. -/
theorem reverse_second_flips_relativeOrientation (I J : EndC) :
    relativeOrientation I (-J) = - relativeOrientation I J := by
  simp [relativeOrientation]

/-- The simultaneous reversal is an exact deck symmetry of the relative character. -/
theorem diagonal_reversal_package (I J : EndC) :
    relativeOrientation (-I) (-J) = relativeOrientation I J ∧
    relativeOrientation (-I) J = - relativeOrientation I J ∧
    relativeOrientation I (-J) = - relativeOrientation I J := by
  exact ⟨reverse_both_preserves_relativeOrientation I J,
    reverse_first_flips_relativeOrientation I J,
    reverse_second_flips_relativeOrientation I J⟩

end GppTwoComplexStructureTemporalOrientation
