import Mathlib.Tactic
import GppVerify.StandardModel.MassOrientationCoupling

/-!
# Spinor-helicity mass bridge

This isolates the exact bridge used in the Grassmannian interpretation.  The
massive momentum factorization already proved in `MassOrientationCoupling`
shows that the symplectic area of the two spinor roots has squared norm equal
to the timelike momentum determinant.  With the standard positive mass-shell
normalization `m^2 = det p`, its norm is therefore exactly `m`.
-/

namespace GppMassOrientationCoupling

/-- Symplectic area of the two explicit spinor roots. -/
noncomputable def spinorArea (p00 p11 : ℝ) (p01 : ℂ) : ℂ :=
  (lambda1 p00 p01).1 * (lambda2 p00 p11 p01).2
    - (lambda1 p00 p01).2 * (lambda2 p00 p11 p01).1

/-- The squared spinor area is exactly the determinant of the Hermitian
momentum matrix. -/
theorem spinorArea_normSq_eq_momentumDet
    {p00 p11 : ℝ} {p01 : ℂ}
    (hp00 : 0 < p00) (hdet : 0 < p00 * p11 - Complex.normSq p01) :
    Complex.normSq (spinorArea p00 p11 p01)
      = p00 * p11 - Complex.normSq p01 := by
  have h := momentum_spinor_decomposition hp00 hdet
  simpa [spinorArea] using h.2.2.2

/-- On the positive mass shell `m^2 = det p`, the modulus of the spinor
symplectic area is exactly the physical mass `m`.  This is the precise
square-root bridge between `det p = m^2` and a spinor-pair determinant of
modulus `m`. -/
theorem spinorArea_norm_eq_mass
    {p00 p11 m : ℝ} {p01 : ℂ}
    (hp00 : 0 < p00) (hdet : 0 < p00 * p11 - Complex.normSq p01)
    (hm : 0 ≤ m)
    (hmass : m ^ 2 = p00 * p11 - Complex.normSq p01) :
    ‖spinorArea p00 p11 p01‖ = m := by
  have harea := spinorArea_normSq_eq_momentumDet hp00 hdet
  have hsq : ‖spinorArea p00 p11 p01‖ ^ 2 = m ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, harea, ← hmass]
  nlinarith [norm_nonneg (spinorArea p00 p11 p01)]

end GppMassOrientationCoupling
