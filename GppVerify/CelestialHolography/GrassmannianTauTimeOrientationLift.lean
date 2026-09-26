import Mathlib.Tactic
import GppVerify.CelestialHolography.GrassmannianRelativeCenterOrientation

/-!
# The Grassmannian tau map is a square root of relative-center spacetime inversion

On the nonsingular Gr(2,4) big cell the project already proves

  tau^2(A) = -A,
  tau^4(A) = A.

The new relative-center analysis identifies `-A` much more precisely: because `A` carries
one left and one right spinor index, a one-sided central sign acts as

  centerAct(-1,+1) A = -A,

while the diagonal center acts trivially.  Therefore

  tau^2 = relative-center orientation reversal

on the big-cell mixed-spinor coordinate.

This is stronger than merely saying `tau` has order four.  It says the halfway point of
the Grassmannian cycle is exactly the nontrivial vector/worldline-orientation coset of the
doubled spin center.  The physical interpretation of `A` as a Lorentzian spacetime/momentum
coordinate still requires the appropriate real slice, but the algebraic identification is
exact.
-/

namespace GppGrassmannianTauTimeOrientationLift

open GppGrassmannianGooglyDecomposition
open GppGrassmannianRelativeCenterOrientation

/-- Main theorem: two tau applications equal either one-sided relative-center action. -/
theorem tau_sq_eq_left_relative_center
    (A : M2) (hD : det2 A ≠ 0) :
    tau (tau A) = centerActM2 (-1) 1 A := by
  rw [tau_sq_from_complement A hD]
  rcases A with ⟨a,b,c,d⟩
  simp [centerActM2, GppSpinProductCenterTimeOrientation.vectorCenterCharacter]

/-- Equivalent right-center lift; the two differ only by the vector-invisible diagonal
spin center. -/
theorem tau_sq_eq_right_relative_center
    (A : M2) (hD : det2 A ≠ 0) :
    tau (tau A) = centerActM2 1 (-1) A := by
  rw [tau_sq_from_complement A hD]
  rcases A with ⟨a,b,c,d⟩
  simp [centerActM2, GppSpinProductCenterTimeOrientation.vectorCenterCharacter]

/-- Thus tau squared reverses the big-cell orientation sign while preserving the determinant. -/
theorem tau_sq_preserves_det_flips_coordinate
    (A : M2) (hD : det2 A ≠ 0) :
    det2 (tau (tau A)) = det2 A ∧
    tau (tau A) = negM2 A := by
  constructor
  · rw [tau_sq_from_complement A hD]
    exact det2_negM2 A
  · simpa [negM2] using tau_sq_from_complement A hD

/-- Four tau applications close, now read as two successive orientation reversals. -/
theorem tau_four_after_orientation_lift
    (A : M2) (hD : det2 A ≠ 0) :
    tau (tau (tau (tau A))) = A := by
  have h2 := tau_sq_from_complement A hD
  have hdet2 : det2 (tau (tau A)) ≠ 0 := by
    rw [h2, show det2 (-A.1,-A.2.1,-A.2.2.1,-A.2.2.2) = det2 A by
      simpa [negM2] using det2_negM2 A]
    exact hD
  rw [tau_sq_from_complement (tau (tau A)) hdet2, h2]
  rcases A with ⟨a,b,c,d⟩
  rfl

end GppGrassmannianTauTimeOrientationLift
