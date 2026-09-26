import GppVerify.CelestialHolography.GrassmannianSelfDuality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# A genuine set-level model of Gr(2,4)

We model `Gr(2,4)` as the type of two-dimensional complex linear subspaces of
the standard Hermitian Euclidean space `C^4 = EuclideanSpace C (Fin 4)`.
This is not yet the full complex manifold / compact homogeneous-space structure,
but it is an actual Grassmannian object rather than a numerical surrogate.

The orthogonal-complement map is then a genuine self-map of this type and an
involution.  This is the precise geometric Z2 used by the later shadow/googly
construction.
-/

namespace GppGrassmannianGr24

open Module

/-- Ambient twistor vector space `C^4`, equipped with its standard Hermitian
`L^2` inner product.  Using `EuclideanSpace` rather than the raw function type
is essential: the raw `Fin 4 → C` type carries the sup norm, while orthogonal
complement requires the compatible Hilbert-space norm. -/
abbrev Ambient := EuclideanSpace ℂ (Fin 4)

/-- `Gr(2,4)` as the type of 2-dimensional complex subspaces of `C^4`. -/
def Gr24 := {K : Submodule ℂ Ambient // finrank ℂ K = 2}

/-- The ambient complex dimension is four. -/
theorem ambient_finrank : finrank ℂ Ambient = 4 := by
  simp [Ambient]

/-- Orthogonal complement sends a point of `Gr(2,4)` to another point of
`Gr(2,4)`. -/
noncomputable def complement (K : Gr24) : Gr24 := by
  let Kperp : Submodule ℂ Ambient := Submodule.orthogonal (𝕜 := ℂ) (E := Ambient) K.1
  refine ⟨Kperp, ?_⟩
  have h := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℂ) (E := Ambient) K.1
  change finrank ℂ Kperp = 2
  dsimp [Kperp]
  rw [K.2, ambient_finrank] at h
  omega

/-- Orthogonal complement is an involution on the actual `Gr24` type. -/
theorem complement_involutive (K : Gr24) : complement (complement K) = K := by
  apply Subtype.ext
  change
    Submodule.orthogonal (𝕜 := ℂ) (E := Ambient)
      (Submodule.orthogonal (𝕜 := ℂ) (E := Ambient) K.1) = K.1
  exact Submodule.orthogonal_orthogonal (𝕜 := ℂ) (E := Ambient) K.1

/-- Hence the complement map is bijective. -/
theorem complement_bijective : Function.Bijective complement := by
  constructor
  · intro A B h
    have h' := congrArg complement h
    simpa only [complement_involutive] using h'
  · intro K
    refine ⟨complement K, ?_⟩
    exact complement_involutive K

/-- The complement operation has no need for an external dual Grassmannian in
middle dimension: it is literally an endomorphism of `Gr(2,4)`. -/
theorem complement_is_self_map (K : Gr24) : complement K ∈ Set.univ := by
  trivial

/-- **Grassmannian shadow.**  In the middle-dimensional twistor Grassmannian
`Gr(2,4)`, the geometric shadow operation is the orthogonal-complement
involution.  This name is the interface used by the celestial/twistor chain. -/
noncomputable def shadow : Gr24 → Gr24 := complement

@[simp] theorem shadow_eq_complement (K : Gr24) : shadow K = complement K := rfl

/-- Shadow squares to the identity on the actual Grassmannian. -/
@[simp] theorem shadow_involutive (K : Gr24) : shadow (shadow K) = K := by
  exact complement_involutive K

/-- The Grassmannian shadow is bijective, with itself as inverse. -/
theorem shadow_bijective : Function.Bijective shadow := by
  simpa [shadow] using complement_bijective

end GppGrassmannianGr24

#print axioms GppGrassmannianGr24.ambient_finrank
#print axioms GppGrassmannianGr24.complement_involutive
#print axioms GppGrassmannianGr24.complement_bijective
#print axioms GppGrassmannianGr24.shadow_involutive
#print axioms GppGrassmannianGr24.shadow_bijective