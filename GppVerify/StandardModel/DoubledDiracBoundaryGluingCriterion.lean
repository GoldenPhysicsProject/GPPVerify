import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic

/-!
# Doubled Dirac boundary gluing: self-adjointness/zero-flux matrix criterion

For two manifolds glued along one hypersurface, the outward normals are opposite.  The
Green boundary form of a first-order Dirac operator therefore has the schematic matrix
coefficient

    G - U^† G U

when the boundary spinors are identified by `psi_- = U psi_+`; here `G` is the normal
Clifford/current matrix on the + side and `U` is the sheet-gluing map.

Thus a sufficient algebraic criterion for cancellation of the two boundary forms is

    U^† G U = G.

The same identity says that the two outward normal currents are equal in magnitude and
opposite in orientation, so the *quotient* has zero net normal fermion flux.  Positive
quadratic energy need not cancel.

This file proves only this finite matrix core.  The analytic theorem that the curved Dirac
operator with this domain is self-adjoint requires the Sobolev trace/domain theory and the
actual CPT spin-bundle intertwiner.
-/

namespace GppDoubledDiracBoundaryGluingCriterion

variable {n : Type} [Fintype n] [DecidableEq n]

abbrev EndC := Matrix n n ℂ

/-- Effective boundary matrix after gluing two opposite-normal sheets. -/
def gluedBoundaryMatrix (G U : EndC) : EndC :=
  G - Matrix.conjTranspose U * G * U

/-- If the gluing map preserves the normal Clifford/current form, the total boundary form
    cancels exactly. -/
theorem boundary_form_cancels_of_preserves_normal_form
    (G U : EndC)
    (hpres : Matrix.conjTranspose U * G * U = G) :
    gluedBoundaryMatrix G U = 0 := by
  rw [gluedBoundaryMatrix, hpres]
  simp

/-- Written with the minus-sheet normal matrix `-G`, the two transported coefficients sum
    to zero under the same condition. -/
theorem opposite_normal_coefficients_cancel
    (G U : EndC)
    (hpres : Matrix.conjTranspose U * G * U = G) :
    G + (-(Matrix.conjTranspose U * G * U)) = 0 := by
  rw [hpres]
  simp

/-- The condition is insensitive to an overall phase of a gluing matrix at the purely
    scalar level: a phase and its conjugate cancel.  This theorem records the scalar core
    used when a physical boundary condition contains an undetermined phase. -/
theorem scalar_phase_cancels (z : ℂ) (hz : star z * z = 1) (g : ℂ) :
    star z * g * z = g := by
  calc
    star z * g * z = (star z * z) * g := by ring
    _ = g := by rw [hz]; simp

end GppDoubledDiracBoundaryGluingCriterion
