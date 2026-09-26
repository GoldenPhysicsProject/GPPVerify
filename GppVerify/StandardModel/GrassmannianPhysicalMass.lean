import Mathlib.Tactic
import GppVerify.StandardModel.SpinorMassBridge

/-!
# Physical mass as the spinor-pair Plucker/chart determinant

The Grassmannian big-cell coordinate is a 2x2 matrix `A`.  When its columns
are the two massive spinor-helicity roots `lambda1, lambda2`, its determinant
is exactly their symplectic area.  Combined with the mass-shell theorem from
`SpinorMassBridge`, this gives `|det A| = m` under the explicit physical
spinor-pair assembly.  It does not identify the determinant of an arbitrary
Grassmannian chart with a measured mass.
-/

namespace GppMassOrientationCoupling

/-- Determinant coordinate of a complex 2x2 big-cell matrix
`[[a,b],[c,d]]`. -/
def complexChartDet (a b c d : ℂ) : ℂ := a * d - b * c

/-- The chart determinant when the two columns are the explicit spinor roots. -/
noncomputable def physicalSpinorChartDet (p00 p11 : ℝ) (p01 : ℂ) : ℂ :=
  complexChartDet
    (lambda1 p00 p01).1 (lambda2 p00 p11 p01).1
    (lambda1 p00 p01).2 (lambda2 p00 p11 p01).2

/-- Column assembly of the spinor pair makes the Grassmannian determinant
exactly the spinor symplectic area. -/
theorem physicalSpinorChartDet_eq_spinorArea
    (p00 p11 : ℝ) (p01 : ℂ) :
    physicalSpinorChartDet p00 p11 p01 = spinorArea p00 p11 p01 := by
  simp [physicalSpinorChartDet, complexChartDet, spinorArea]
  ring

/-- Therefore, on the positive mass shell, the modulus of the physically
assembled chart determinant is exactly the physical mass. -/
theorem physicalSpinorChartDet_norm_eq_mass
    {p00 p11 m : ℝ} {p01 : ℂ}
    (hp00 : 0 < p00) (hdet : 0 < p00 * p11 - Complex.normSq p01)
    (hm : 0 ≤ m)
    (hmass : m ^ 2 = p00 * p11 - Complex.normSq p01) :
    ‖physicalSpinorChartDet p00 p11 p01‖ = m := by
  rw [physicalSpinorChartDet_eq_spinorArea]
  exact spinorArea_norm_eq_mass hp00 hdet hm hmass

end GppMassOrientationCoupling
