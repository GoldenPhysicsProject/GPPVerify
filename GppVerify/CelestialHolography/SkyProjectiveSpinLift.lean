import Mathlib.Tactic
import GppVerify.CelestialHolography.EinsteinScaleProjectiveFiber

/-!
# Central sign in the rank-two sky projective fibre

A one-dimensional projective structure naturally has projective `PSL(2)` transition
functions.  After a theta/spin choice, standard projective-connection theory lifts these
to determinant-one `SL(2)` transition functions on a rank-two solution bundle.

This file formalizes only the elementary finite-dimensional quotient algebra behind that
statement.  The two matrices `M` and `-M` have the same determinant, their actions on a
rank-two solution state differ by the central scalar `-1`, and therefore they induce the
same projective ratio wherever that ratio is defined.  Thus the central `{+I,-I}` sign is
invisible after projectivization.

The existence and global consistency of a theta/spin lift on a curved ray family is
external geometry and is NOT asserted here.
-/

namespace GppSkyProjectiveSpinLift

open GppGrassmannianGooglyDecomposition
open GppEinsteinNullRaySL2Geometry
open GppEinsteinScaleProjectiveFiber

/-- Entrywise central sign on a `2x2` matrix. -/
def negM2 (M : M2) : M2 :=
  (-M.1,-M.2.1,-M.2.2.1,-M.2.2.2)

/-- The central sign does not change the determinant in two dimensions. -/
theorem det2_negM2 (M : M2) : det2 (negM2 M) = det2 M := by
  rcases M with ⟨a,b,c,d⟩
  simp [negM2, det2]
  ring

/-- Therefore an `SL(2)` matrix and its central negative are both determinant one. -/
theorem negM2_det_one_of_det_one (M : M2) (hM : det2 M = 1) :
    det2 (negM2 M) = 1 := by
  rw [det2_negM2, hM]

/-- Central sign on a rank-two solution state. -/
def negState (u : RayState) : RayState := (-u.1,-u.2)

/-- Acting by `-M` is exactly acting by `M` and then multiplying the state by `-1`. -/
theorem act2_negM2 (M : M2) (u : RayState) :
    act2 (negM2 M) u = negState (act2 M u) := by
  rcases M with ⟨a,b,c,d⟩
  rcases u with ⟨x,y⟩
  apply Prod.ext <;> simp [act2, negM2, negState] <;> ring

/-- Multiplying a nonzero projective representative by the central sign leaves its affine
projective ratio unchanged. -/
theorem projectiveRatio_negState (u : RayState) (hu : u.2 ≠ 0) :
    projectiveRatio (negState u) = projectiveRatio u := by
  rcases u with ⟨x,y⟩
  simp [projectiveRatio, negState] at hu ⊢
  field_simp [hu]

/-- Hence `M` and `-M` induce the same projective action wherever the transformed second
component is nonzero. -/
theorem central_sign_same_projective_action
    (M : M2) (u : RayState)
    (hden : (act2 M u).2 ≠ 0) :
    projectiveRatio (act2 (negM2 M) u) = projectiveRatio (act2 M u) := by
  rw [act2_negM2]
  exact projectiveRatio_negState (act2 M u) hden

/-- The standard Weyl representative and its negative therefore define the same
projective inversion, even though they are distinct `SL(2)` lifts. -/
theorem rayWeyl_central_sign_same_projective_action
    (u : RayState) (hden : (act2 rayWeyl u).2 ≠ 0) :
    projectiveRatio (act2 (negM2 rayWeyl) u) =
      projectiveRatio (act2 rayWeyl u) :=
  central_sign_same_projective_action rayWeyl u hden

end GppSkyProjectiveSpinLift
