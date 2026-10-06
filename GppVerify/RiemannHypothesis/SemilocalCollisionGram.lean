import GppVerify.RiemannHypothesis.GramPositivityBoundary

/-!
# Semilocal collision Gram positivity

Source: Codex, RH_EULER_ARCHIMEDEAN_COLLISION_2026-10-05.md, Section 2.

The semilocal CCM collision defect is represented by vectors of the form

  g_i = e_i - T e_i

in the ambient whole-line Hilbert space, where T is translation. Once the
explicit overlap calculation identifies the matrix entries with
<g_i,g_j>, positivity is ordinary Gram positivity.

This file records exactly that abstract finite Hilbert-space step. It does
not formalize the explicit interval exponential overlap formula, the
Archimedean integral, or any global RH statement.
-/

namespace GppSemilocalCollisionGram

variable {V ι : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Collision vectors associated with an isometric translation/transport. -/
noncomputable def collisionVec
    (T : V →ₗᵢ[ℂ] V) (v : ι → V) (i : ι) : V :=
  v i - T (v i)

/-- Any finite matrix of collision-vector inner products has nonnegative
quadratic form. This is the abstract positivity used after identifying the
semilocal defect with the Gram matrix of e_n - T_y e_n. -/
theorem collision_quadratic_nonneg
    (T : V →ₗᵢ[ℂ] V) (v : ι → V)
    (S : Finset ι) (c : ι → ℂ) :
    0 ≤
      (∑ i ∈ S, ∑ j ∈ S,
        starRingEnd ℂ (c i) * c j *
          (inner ℂ (collisionVec T v i) (collisionVec T v j) : ℂ)).re := by
  exact GppYakaboylu.gram_posSemidef S (collisionVec T v) c

/-- The one-vector collision energy is nonnegative. -/
theorem collision_energy_nonneg
    (T : V →ₗᵢ[ℂ] V) (f : V) :
    0 ≤ ‖f - T f‖ ^ 2 := by
  positivity

end GppSemilocalCollisionGram

#print axioms GppSemilocalCollisionGram.collision_quadratic_nonneg
#print axioms GppSemilocalCollisionGram.collision_energy_nonneg
