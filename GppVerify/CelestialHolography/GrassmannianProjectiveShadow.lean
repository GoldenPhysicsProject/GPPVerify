import GppVerify.CelestialHolography.GrassmannianPluckerProjective
import Mathlib.Data.Quot
import Mathlib.Tactic

/-!
# Quotient-level projective Shadow on Plücker bivectors

`GrassmannianPluckerProjective` proves that the antiunitary googly exchange preserves
nonzero complex rescaling of Plücker bivectors.  Here we complete that descent: first
prove that the rescaling relation is an equivalence relation, then quotient by it, and
construct the induced Shadow map on the quotient.  The resulting map is an involution.

The quotient below includes the distinguished zero class.  Thus it is the affine
bivector cone modulo nonzero scale, rather than literally projective space `CP^5`.
Restricting to nonzero decomposable bivectors (the actual Klein quadric) is the next
geometric layer; no identification with the submodule model `Gr24` is asserted here.
-/

namespace GppGrassmannianProjectiveShadow

open GppGooglyAntiunitaryExchange GppGrassmannianPluckerProjective

/-- Projective rescaling is reflexive. -/
theorem projectivelyEquivalent_refl (v : Fin 6 → ℂ) :
    ProjectivelyEquivalent v v := by
  refine ⟨1, one_ne_zero, ?_⟩
  simp

/-- Projective rescaling is symmetric. -/
theorem projectivelyEquivalent_symm {v w : Fin 6 → ℂ}
    (h : ProjectivelyEquivalent v w) : ProjectivelyEquivalent w v := by
  rcases h with ⟨c, hc, rfl⟩
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  simp [hc]

/-- Projective rescaling is transitive. -/
theorem projectivelyEquivalent_trans {u v w : Fin 6 → ℂ}
    (huv : ProjectivelyEquivalent u v) (hvw : ProjectivelyEquivalent v w) :
    ProjectivelyEquivalent u w := by
  rcases huv with ⟨c, hc, rfl⟩
  rcases hvw with ⟨d, hd, rfl⟩
  refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
  simp [mul_smul]

/-- The nonzero-scaling relation as an honest setoid. -/
def projectiveSetoid : Setoid (Fin 6 → ℂ) where
  r := ProjectivelyEquivalent
  iseqv := ⟨projectivelyEquivalent_refl, projectivelyEquivalent_symm,
    projectivelyEquivalent_trans⟩

/-- Bivectors modulo nonzero complex scale, with a distinguished zero class. -/
abbrev ScaledBivectorQuotient := Quotient projectiveSetoid

/-- The antiunitary googly exchange descends to the quotient by complex scale. -/
def projectiveShadow : ScaledBivectorQuotient → ScaledBivectorQuotient :=
  Quotient.map googlyExchange (by
    intro a b hab
    exact googlyExchange_preserves_projective_equivalence hab)

/-- On representatives, quotient Shadow is exactly the googly exchange. -/
@[simp] theorem projectiveShadow_mk (v : Fin 6 → ℂ) :
    projectiveShadow (Quotient.mk projectiveSetoid v) =
      Quotient.mk projectiveSetoid (googlyExchange v) := rfl

/-- **Projective Shadow is a genuine involution on the quotient.** -/
@[simp] theorem projectiveShadow_involutive (q : ScaledBivectorQuotient) :
    projectiveShadow (projectiveShadow q) = q := by
  refine Quotient.inductionOn q ?_
  intro v
  simp [projectiveShadow, googlyExchange_involutive]

/-- Consequently the quotient-level Shadow map is bijective. -/
theorem projectiveShadow_bijective : Function.Bijective projectiveShadow := by
  constructor
  · intro a b h
    have h' := congrArg projectiveShadow h
    simpa only [projectiveShadow_involutive] using h'
  · intro q
    exact ⟨projectiveShadow q, projectiveShadow_involutive q⟩

end GppGrassmannianProjectiveShadow

#print axioms GppGrassmannianProjectiveShadow.projectivelyEquivalent_refl
#print axioms GppGrassmannianProjectiveShadow.projectivelyEquivalent_symm
#print axioms GppGrassmannianProjectiveShadow.projectivelyEquivalent_trans
#print axioms GppGrassmannianProjectiveShadow.projectiveShadow_involutive
#print axioms GppGrassmannianProjectiveShadow.projectiveShadow_bijective
