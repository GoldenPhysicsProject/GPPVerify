import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation
import GppVerify.StandardModel.HorizonOrientationBranchedDoubleCover

/-!
# Folded black-mirror CPT core: embedding time fixed, sheet and sphere orientation reversed

Tzanavaris--Boyle--Turok's stationary black-mirror CPT isometry is written in their folded
coordinates as

    (t, sigma, theta, phi) -> (t, -sigma, pi-theta, phi+pi).

The key point for the present orientation programme is that the displayed embedding-time
coordinate `t` is unchanged: in the folded Penrose diagram, time runs upward in the usual
direction on both sheets.  What changes is the sheet coordinate `sigma` and the orientation
of the angular two-sphere.  The latter is why Gauss-law electric charge changes sign even
though the local field-strength two-form is invariant under the spacetime isometry.

This module machine-checks the elementary coordinate/orientation core:

* `t` is fixed;
* `sigma` changes sign but the Schwarzschild base radius r(sigma) is unchanged;
* the angular Jacobian diag(-1,+1) has determinant -1, so the S^2 orientation reverses;
* a flux sign defined relative to that oriented sphere changes sign;
* applying the folded map twice returns the original sheet and angular orientation (modulo
  the usual 2pi periodicity of phi, represented here only at the sign/Jacobian level).

This does NOT yet identify the sheet sign with the charged-CAR dynamical complex orientation
J.  That is the next required intertwiner.
-/

namespace GppBlackMirrorFoldedCPTOrientation

open GppHorizonOrientationBranchedDoubleCover

/-- Finite sign carrier: embedding-time orientation, sheet sign, sphere orientation sign. -/
abbrev FoldSigns := Bool × Bool × Bool

/-- Folded black-mirror CPT sign core: leave embedding time alone; reverse sheet and sphere. -/
def foldedCPTSigns (x : FoldSigns) : FoldSigns :=
  (x.1, !x.2.1, !x.2.2)

/-- The displayed embedding-time orientation is unchanged. -/
theorem foldedCPT_preserves_embedding_time (x : FoldSigns) :
    (foldedCPTSigns x).1 = x.1 := by rfl

/-- Sheet and angular orientation both reverse. -/
theorem foldedCPT_flips_sheet_and_sphere (x : FoldSigns) :
    (foldedCPTSigns x).2.1 = !x.2.1 ∧
    (foldedCPTSigns x).2.2 = !x.2.2 := by rfl

/-- The folded sign map is involutive. -/
theorem foldedCPT_sq (x : FoldSigns) : foldedCPTSigns (foldedCPTSigns x) = x := by
  rcases x with ⟨t,s,o⟩
  cases t <;> cases s <;> cases o <;> rfl

/-- The actual radial base coordinate cannot distinguish sigma from -sigma. -/
theorem foldedCPT_same_base_radius (m sigma : ℝ) :
    mirrorRadius m (-sigma) = mirrorRadius m sigma := by
  simpa [sheetFlip] using mirrorRadius_sheetFlip m sigma

/-- Linear angular Jacobian of (theta,phi)->(pi-theta,phi+pi). -/
def angularJacobian : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1,0;0,1]

/-- Its determinant is -1: the angular two-sphere orientation reverses. -/
theorem angularJacobian_det_negative : Matrix.det angularJacobian = -1 := by
  norm_num [angularJacobian, Matrix.det_fin_two]

/-- Represent an oriented Gauss flux only by its sign.  Reversing the integration-sphere
    orientation reverses the measured flux/charge sign. -/
def reverseFluxSign (q : ℝ) : ℝ := -q

 theorem sphere_orientation_flip_reverses_Gauss_sign (q : ℝ) :
    reverseFluxSign q = -q := by rfl

/-- Reversing the sphere orientation twice restores the original Gauss sign. -/
theorem sphere_orientation_flip_twice (q : ℝ) :
    reverseFluxSign (reverseFluxSign q) = q := by
  simp [reverseFluxSign]

/-- Capstone: folded black-mirror CPT can reverse the sheet and measured Gauss charge while
    leaving the common embedding-time direction untouched and the base radius unchanged. -/
theorem folded_black_mirror_orientation_capstone
    (m sigma q : ℝ) (x : FoldSigns) :
    (foldedCPTSigns x).1 = x.1 ∧
    mirrorRadius m (-sigma) = mirrorRadius m sigma ∧
    Matrix.det angularJacobian = -1 ∧
    reverseFluxSign q = -q := by
  exact ⟨foldedCPT_preserves_embedding_time x,
    foldedCPT_same_base_radius m sigma,
    angularJacobian_det_negative,
    rfl⟩

end GppBlackMirrorFoldedCPTOrientation
