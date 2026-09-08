import Mathlib.Tactic
import GppVerify.StandardModel.GrassmannianPhysicalMass

/-!
# Massive spinor-root orientation reversal preserves physical mass

A positive timelike momentum is represented in the current massive spinor-helicity bridge
by two spinor roots `lambda1,lambda2`.  Their ordered symplectic area is the determinant of
the corresponding `2x2` Grassmannian chart and has modulus equal to the positive mass.

The ordered pair carries more information than the mass: exchanging the two roots reverses
its orientation and negates the determinant,

    det[lambda2 lambda1] = - det[lambda1 lambda2],

while leaving its modulus unchanged.  Therefore the physical mass is blind to this
orientation reversal.

This is the precise elementary massive analogue of an orientation/factor exchange: the
oriented square root changes sign, while the invariant timelike norm does not.  It does
NOT identify the two orientations with particle/antiparticle or with CPT by itself; those
identifications require the representation-theoretic and gauge-charge bridges.
-/

namespace GppMassiveSpinorOrientationFlip

open GppMassOrientationCoupling

/-- Determinant of the physically assembled spinor pair with the two roots exchanged. -/
noncomputable def swappedPhysicalSpinorChartDet
    (p00 p11 : ℝ) (p01 : ℂ) : ℂ :=
  complexChartDet
    (lambda2 p00 p11 p01).1 (lambda1 p00 p01).1
    (lambda2 p00 p11 p01).2 (lambda1 p00 p01).2

/-- Exchanging the two massive spinor roots reverses the oriented determinant exactly. -/
theorem swappedPhysicalSpinorChartDet_eq_neg
    (p00 p11 : ℝ) (p01 : ℂ) :
    swappedPhysicalSpinorChartDet p00 p11 p01 =
      - physicalSpinorChartDet p00 p11 p01 := by
  simp [swappedPhysicalSpinorChartDet, physicalSpinorChartDet,
    complexChartDet]
  ring

/-- Consequently the determinant modulus is completely insensitive to root orientation. -/
theorem swappedPhysicalSpinorChartDet_norm_eq
    (p00 p11 : ℝ) (p01 : ℂ) :
    ‖swappedPhysicalSpinorChartDet p00 p11 p01‖ =
      ‖physicalSpinorChartDet p00 p11 p01‖ := by
  rw [swappedPhysicalSpinorChartDet_eq_neg]
  simp

/-- On the positive mass shell, the oppositely oriented spinor pair has exactly the same
physical mass. -/
theorem swappedPhysicalSpinorChartDet_norm_eq_mass
    {p00 p11 m : ℝ} {p01 : ℂ}
    (hp00 : 0 < p00)
    (hdet : 0 < p00 * p11 - Complex.normSq p01)
    (hm : 0 ≤ m)
    (hmass : m ^ 2 = p00 * p11 - Complex.normSq p01) :
    ‖swappedPhysicalSpinorChartDet p00 p11 p01‖ = m := by
  rw [swappedPhysicalSpinorChartDet_norm_eq]
  exact physicalSpinorChartDet_norm_eq_mass hp00 hdet hm hmass

/-- At the abstract two-column level, exchange is an involution. -/
def swapSpinorPair (u v : ℂ × ℂ) : (ℂ × ℂ) × (ℂ × ℂ) := (v,u)

theorem swapSpinorPair_involution (u v : ℂ × ℂ) :
    let p := swapSpinorPair u v
    swapSpinorPair p.1 p.2 = (u,v) := by
  rfl

/-- The generic symplectic area of an ordered two-spinor pair. -/
def orderedSpinorArea (u v : ℂ × ℂ) : ℂ :=
  u.1*v.2-u.2*v.1

/-- The oriented square root is odd under root exchange. -/
theorem orderedSpinorArea_swap (u v : ℂ × ℂ) :
    orderedSpinorArea v u = - orderedSpinorArea u v := by
  simp [orderedSpinorArea]
  ring

/-- Its norm, the massive invariant, is even under the same exchange. -/
theorem orderedSpinorArea_norm_swap (u v : ℂ × ℂ) :
    ‖orderedSpinorArea v u‖ = ‖orderedSpinorArea u v‖ := by
  rw [orderedSpinorArea_swap]
  simp

end GppMassiveSpinorOrientationFlip
