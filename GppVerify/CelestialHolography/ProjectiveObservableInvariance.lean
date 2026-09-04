import Mathlib.Tactic
import GppVerify.CelestialHolography.ProjectiveOrientationInvariance

/-!
# Observable invariance on projective orientation orbits

The previous module shows that orientation reversal changes a split-Hodge Plucker
representative only by the central projective sign.  Here we formulate the operational
consequence: any observable which descends to projective Grassmannian space assigns
the same value to the two representatives.

This gives a concrete finite-dimensional realization of the quotient statement
`[x]=[Dx]` for orientation reversal at the Plucker level.
-/

namespace GppProjectiveObservableInvariance

open GppGrassmannianGooglyDecomposition
open GppSplitSignatureHodgeGrassmannian
open GppProjectiveOrientationInvariance

/-- An observable on homogeneous Plucker representatives which depends only on the
projective point.  Scale invariance is required only for nonzero real scales. -/
structure ProjectiveObservable (Obs : Type*) where
  observe : P6 → Obs
  scale_invariant : ∀ (λ : ℝ), λ ≠ 0 → ∀ p,
    observe (scaleP6 λ p) = observe p

namespace ProjectiveObservable

variable {Obs : Type*} (O : ProjectiveObservable Obs)

/-- Projectively equivalent representatives have the same observable value. -/
theorem eq_on_projectivelyEquivalent
    {p q : P6} (h : ProjectivelyEquivalent p q) :
    O.observe q = O.observe p := by
  rcases h with ⟨λ,hλ,rfl⟩
  exact O.scale_invariant λ hλ p

/-- Orientation reversal does not change any projective observable of the Hodge
complement: `star p` and `-star p` are observationally identical downstairs. -/
theorem reversed_hodge_same_observable (p : P6) :
    O.observe (scaleP6 (-1) (splitStar p)) = O.observe (splitStar p) := by
  exact O.scale_invariant (-1) (by norm_num) (splitStar p)

/-- For an SD representative, the reversed-orientation ASD representative has exactly
the same projective observable value as the original field representative. -/
theorem sd_asd_orientation_pair_same_observable
    (p : P6) (hSD : splitStar p = p) :
    O.observe (scaleP6 (-1) (splitStar p)) = O.observe p := by
  rw [hSD]
  exact O.scale_invariant (-1) (by norm_num) p

/-- Quotient/orbit formulation: if two representatives differ by the orientation
central sign, every projective observable identifies them. -/
theorem orientation_orbit_operationally_indistinguishable (p : P6) :
    O.observe (scaleP6 (-1) p) = O.observe p := by
  exact O.scale_invariant (-1) (by norm_num) p

end ProjectiveObservable

end GppProjectiveObservableInvariance
