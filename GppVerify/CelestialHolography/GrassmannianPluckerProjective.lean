import GppVerify.CelestialHolography.GooglyAntiunitaryExchange
import Mathlib.Tactic

/-!
# Projective covariance of Plücker coordinates

The existing holographic-chain file proves the Plücker relation for a chosen ordered
pair `(v1,v2)` in `ℂ^4`.  To descend from a frame to the Grassmannian point represented
by that frame, one needs the basis-change law: under a `2 × 2` change of frame, all six
Plücker coordinates acquire the same determinant factor.  Therefore their projective
class is frame-independent whenever the change of frame is invertible.

The antiunitary googly exchange is conjugate-linear on this common scale.  Hence it
respects projective equivalence and defines an involution on projective Plücker classes;
combined with preservation of the Plücker quadric, this is the algebraic projective
shadow on the Klein quadric.
-/

namespace GppGrassmannianPluckerProjective

open GppHolographicChain GppGooglyAntiunitaryExchange

/-- A general linear recombination of a two-vector frame. -/
def frameChange
    (a b c d : ℂ) (v1 v2 : Fin 4 → ℂ) : (Fin 4 → ℂ) × (Fin 4 → ℂ) :=
  (fun i => a * v1 i + b * v2 i,
   fun i => c * v1 i + d * v2 i)

/-- **Plücker determinant covariance.**  Every Plücker coordinate of a changed
2-frame is multiplied by the same determinant `a*d - b*c`. -/
theorem plucker_frameChange
    (a b c d : ℂ) (v1 v2 : Fin 4 → ℂ) (i j : Fin 4) :
    let w := frameChange a b c d v1 v2
    plucker w.1 w.2 i j = (a * d - b * c) * plucker v1 v2 i j := by
  dsimp [frameChange, plucker]
  ring

/-- If the frame change has determinant one, the Plücker coordinates are literally
unchanged. -/
theorem plucker_sl2_invariant
    {a b c d : ℂ} (hdet : a * d - b * c = 1)
    (v1 v2 : Fin 4 → ℂ) (i j : Fin 4) :
    let w := frameChange a b c d v1 v2
    plucker w.1 w.2 i j = plucker v1 v2 i j := by
  dsimp only
  rw [plucker_frameChange]
  simp [hdet]

/-- For an invertible frame change, the common Plücker scale is nonzero. -/
theorem plucker_common_scale_ne_zero
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) :
    a * d - b * c ≠ 0 := hdet

/-- The Plücker quadratic relation is preserved under every frame change, because
all six coordinates acquire the same common determinant factor.  Here it is stated
at the level of the transformed frame, so it follows from the unconditional relation
already proved for arbitrary vectors. -/
theorem plucker_relation_frameChange
    (a b c d : ℂ) (v1 v2 : Fin 4 → ℂ) :
    let w := frameChange a b c d v1 v2
    plucker w.1 w.2 0 1 * plucker w.1 w.2 2 3
      - plucker w.1 w.2 0 2 * plucker w.1 w.2 1 3
      + plucker w.1 w.2 0 3 * plucker w.1 w.2 1 2 = 0 := by
  dsimp [frameChange]
  exact plucker_relation _ _

/-- The six-coordinate Plücker vector transforms by one common determinant scale. -/
theorem pluckerVector_frameChange
    (a b c d : ℂ) (v1 v2 : Fin 4 → ℂ) :
    let w := frameChange a b c d v1 v2
    pluckerVector w.1 w.2 = (a * d - b * c) • pluckerVector v1 v2 := by
  dsimp only
  ext i
  fin_cases i <;>
    simp [pluckerVector, plucker_frameChange, Pi.smul_apply]

/-- Two nonzero-scale bivectors represent the same projective Plücker point. -/
def ProjectivelyEquivalent (v w : Fin 6 → ℂ) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ w = c • v

/-- An invertible change of two-frame does not change its projective Plücker point. -/
theorem frameChange_projectivelyEquivalent
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0)
    (v1 v2 : Fin 4 → ℂ) :
    let w := frameChange a b c d v1 v2
    ProjectivelyEquivalent (pluckerVector v1 v2) (pluckerVector w.1 w.2) := by
  dsimp only
  refine ⟨a * d - b * c, hdet, ?_⟩
  exact pluckerVector_frameChange a b c d v1 v2

/-- **Projective descent of the antiunitary googly exchange.**  If two Plücker
vectors differ by a nonzero complex scale, their googly images differ by the
conjugate nonzero scale.  Thus the antiunitary exchange is well-defined on
projective Plücker classes. -/
theorem googlyExchange_preserves_projective_equivalence
    {v w : Fin 6 → ℂ} (h : ProjectivelyEquivalent v w) :
    ProjectivelyEquivalent (googlyExchange v) (googlyExchange w) := by
  rcases h with ⟨c, hc, rfl⟩
  refine ⟨star c, ?_, ?_⟩
  · intro hz
    apply hc
    have hz' := congrArg star hz
    simpa using hz'
  · exact googlyExchange_smul c v

/-- Because the googly exchange is itself an involution, projective equivalence is
preserved in both directions. -/
theorem googlyExchange_projective_equivalence_iff (v w : Fin 6 → ℂ) :
    ProjectivelyEquivalent (googlyExchange v) (googlyExchange w) ↔
      ProjectivelyEquivalent v w := by
  constructor
  · intro h
    have h' := googlyExchange_preserves_projective_equivalence h
    simpa only [googlyExchange_involutive] using h'
  · exact googlyExchange_preserves_projective_equivalence

/-- The full projective Klein-quadric statement: projective representatives remain
projectively equivalent after googly exchange, and any representative on the Plücker
quadric is sent to another representative on the same quadric. -/
theorem googlyExchange_projective_klein_quadric
    {v w : Fin 6 → ℂ}
    (hproj : ProjectivelyEquivalent v w) (hv : pluckerQuadric v = 0) :
    ProjectivelyEquivalent (googlyExchange v) (googlyExchange w) ∧
      pluckerQuadric (googlyExchange v) = 0 := by
  exact ⟨googlyExchange_preserves_projective_equivalence hproj,
    googlyExchange_preserves_plucker_quadric hv⟩

end GppGrassmannianPluckerProjective

#print axioms GppGrassmannianPluckerProjective.plucker_frameChange
#print axioms GppGrassmannianPluckerProjective.plucker_sl2_invariant
#print axioms GppGrassmannianPluckerProjective.plucker_relation_frameChange
#print axioms GppGrassmannianPluckerProjective.pluckerVector_frameChange
#print axioms GppGrassmannianPluckerProjective.frameChange_projectivelyEquivalent
#print axioms GppGrassmannianPluckerProjective.googlyExchange_preserves_projective_equivalence
#print axioms GppGrassmannianPluckerProjective.googlyExchange_projective_equivalence_iff
#print axioms GppGrassmannianPluckerProjective.googlyExchange_projective_klein_quadric
