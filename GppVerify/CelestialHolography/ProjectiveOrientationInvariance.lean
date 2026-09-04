import Mathlib.Tactic
import GppVerify.CelestialHolography.SplitSignatureHodgeGrassmannian

/-!
# Projective orientation invariance of the split Hodge complement

Reversing orientation changes the Hodge operator from `star` to `-star`.  On
projective Plucker space, however, `p` and `-p` determine the same point.  Therefore
orientation reversal flips the SD/ASD eigenvalue label without changing the
underlying projective Grassmannian point selected by the complement.

This is a precise finite-dimensional version of the statement "same geometry,
opposite chirality label".  It does not identify orientation reversal with CPT or
with a dynamical time-reversal operator.
-/

namespace GppProjectiveOrientationInvariance

open GppGrassmannianGooglyDecomposition
open GppSplitSignatureHodgeGrassmannian

/-- Coordinate scaling on Plucker six-vectors. -/
def scaleP6 (λ : ℝ) (p : P6) : P6 :=
  ⟨λ*p.p01, λ*p.p02, λ*p.p03, λ*p.p12, λ*p.p13, λ*p.p23⟩

/-- Elementary projective equivalence: two nonzero homogeneous representatives may
differ by any nonzero real scale.  This relation is sufficient for the orientation
comparison below; no quotient type is introduced. -/
def ProjectivelyEquivalent (p q : P6) : Prop :=
  ∃ λ : ℝ, λ ≠ 0 ∧ q = scaleP6 λ p

/-- Every Plucker vector is projectively equivalent to itself. -/
theorem projectivelyEquivalent_refl (p : P6) : ProjectivelyEquivalent p p := by
  refine ⟨1, one_ne_zero, ?_⟩
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [scaleP6]

/-- Multiplication by the central sign does not change the projective point. -/
theorem neg_same_projective_point (p : P6) :
    ProjectivelyEquivalent p (scaleP6 (-1) p) := by
  exact ⟨-1, by norm_num, rfl⟩

/-- Reversing orientation sends the split Hodge representative `star p` to `-star p`,
but these are the same projective Plucker point. -/
theorem reversed_hodge_same_projective_complement (p : P6) :
    ProjectivelyEquivalent (splitStar p) (scaleP6 (-1) (splitStar p)) :=
  neg_same_projective_point (splitStar p)

/-- If `p` is self-dual for one orientation, the reversed-orientation Hodge image is
`-p`; projectively this is still the same underlying Grassmannian point. -/
theorem sd_becomes_asd_same_projective_point
    (p : P6) (hSD : splitStar p = p) :
    scaleP6 (-1) (splitStar p) = scaleP6 (-1) p ∧
    ProjectivelyEquivalent p (scaleP6 (-1) (splitStar p)) := by
  constructor
  · rw [hSD]
  · rw [hSD]
    exact neg_same_projective_point p

/-- The same statement in eigenvalue language: a `+1` Hodge eigenvector for one
orientation is a `-1` eigenvector for the reversed orientation, while its projective
representative is unchanged. -/
theorem same_geometry_opposite_chirality_label
    (p : P6) (hSD : splitStar p = p) :
    scaleP6 (-1) (splitStar p) = scaleP6 (-1) p ∧
    ProjectivelyEquivalent p (scaleP6 (-1) p) := by
  exact ⟨by rw [hSD], neg_same_projective_point p⟩

end GppProjectiveOrientationInvariance
