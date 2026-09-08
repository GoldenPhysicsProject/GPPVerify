import Mathlib.Tactic
import GppVerify.CelestialHolography.SpinProductCenterTimeOrientation

/-!
# Massive momentum inherits the relative spin-center orientation sign

A timelike/massive momentum can be written as a sum of two rank-one null spinor products,

  P = lambda1*lambdatilde1^T + lambda2*lambdatilde2^T.

Apply the nontrivial relative center by flipping the sign of every LEFT spinor while leaving
the right spinors fixed.  Each rank-one term changes sign, hence

  P -> -P.

The same occurs if the right spinors are flipped instead.  But for a 2x2 momentum matrix

  det(-P) = det(P),

so the invariant mass square is unchanged.  Thus the relative center reverses the oriented
four-momentum/worldline direction while preserving mass.

This is the massive analogue of the null result in `SpinProductCenterTimeOrientation`.
It gives a clean finite distinction between `mass` and the proposed time/worldline
orientation bit: mass is even, momentum orientation is odd.
-/

namespace GppMassiveSpinCenterOrientation

open GppFlatInfinityCelestialFactorization
open GppSpinProductCenterTimeOrientation
open GppGrassmannianGooglyDecomposition

/-- Coordinate addition for the project's 2x2 carrier. -/
def addM2 (A B : M2) : M2 :=
  (A.1+B.1, A.2.1+B.2.1, A.2.2.1+B.2.2.1, A.2.2.2+B.2.2.2)

/-- Massive/timelike momentum represented as a sum of two null spinor dyads. -/
def massiveMomentumFromTwoNull
    (l1 lt1 l2 lt2 : Spinor2) : M2 :=
  addM2 (nullMomentum l1 lt1) (nullMomentum l2 lt2)

/-- Scaling distributes over coordinate addition. -/
theorem scaleM2_add (r : ℝ) (A B : M2) :
    scaleM2 r (addM2 A B) = addM2 (scaleM2 r A) (scaleM2 r B) := by
  rcases A with ⟨a,b,c,d⟩
  rcases B with ⟨e,f,g,h⟩
  apply Prod.ext
  · simp [scaleM2, addM2]; ring
  · apply Prod.ext
    · simp [scaleM2, addM2]; ring
    · apply Prod.ext
      · simp [scaleM2, addM2]; ring
      · simp [scaleM2, addM2]; ring

/-- Flipping the relative center on the left reverses the entire massive momentum. -/
theorem left_center_flip_reverses_massive_momentum
    (l1 lt1 l2 lt2 : Spinor2) :
    massiveMomentumFromTwoNull (centerScale (-1) l1) lt1
      (centerScale (-1) l2) lt2 =
      scaleM2 (-1) (massiveMomentumFromTwoNull l1 lt1 l2 lt2) := by
  simp [massiveMomentumFromTwoNull, addM2,
    left_center_flip_reverses_vector, scaleM2]

/-- The right-center implementation gives the same oriented momentum reversal. -/
theorem right_center_flip_reverses_massive_momentum
    (l1 lt1 l2 lt2 : Spinor2) :
    massiveMomentumFromTwoNull l1 (centerScale (-1) lt1)
      l2 (centerScale (-1) lt2) =
      scaleM2 (-1) (massiveMomentumFromTwoNull l1 lt1 l2 lt2) := by
  simp [massiveMomentumFromTwoNull, addM2,
    right_center_flip_reverses_vector, scaleM2]

/-- Negating a 2x2 momentum matrix leaves its determinant invariant. -/
theorem det2_neg_invariant (P : M2) :
    det2 (scaleM2 (-1) P) = det2 P := by
  rcases P with ⟨a,b,c,d⟩
  simp [scaleM2, det2]
  ring

/-- Therefore the massive invariant `det P` is even under relative-center/time orientation
reversal. -/
theorem massSq_preserved_under_left_center_flip
    (l1 lt1 l2 lt2 : Spinor2) :
    det2 (massiveMomentumFromTwoNull (centerScale (-1) l1) lt1
      (centerScale (-1) l2) lt2) =
    det2 (massiveMomentumFromTwoNull l1 lt1 l2 lt2) := by
  rw [left_center_flip_reverses_massive_momentum]
  exact det2_neg_invariant _

/-- Same invariant statement for the right-center lift. -/
theorem massSq_preserved_under_right_center_flip
    (l1 lt1 l2 lt2 : Spinor2) :
    det2 (massiveMomentumFromTwoNull l1 (centerScale (-1) lt1)
      l2 (centerScale (-1) lt2)) =
    det2 (massiveMomentumFromTwoNull l1 lt1 l2 lt2) := by
  rw [right_center_flip_reverses_massive_momentum]
  exact det2_neg_invariant _

end GppMassiveSpinCenterOrientation
