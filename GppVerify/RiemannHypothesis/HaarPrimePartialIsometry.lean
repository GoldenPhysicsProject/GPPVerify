import Mathlib.Tactic

/-!
# Haar unramified projector and Dirichlet prime vertex: abstract Fourier algebra

Source: Daniel Toupin's compact norm-one idele/Peter-Weyl programme,
Codex/GPT 2026-10-15:
GPP-bridge/work/codex/2026-10-15_prime_local_haar_partial_isometry_GRH_sectors.md

In the compact K character decomposition a prime p acts by the phase
eta(p), which is a root of unity when p is unramified and ZERO when p
divides the conductor. Therefore the Euler prime vertex is a partial
isometry, NOT a universal unitary.

Here I is an arbitrary index type of character sectors, P denotes the
p-unramified sector predicate, and w denotes the primitive Euler
coefficients. Under the precise phase/ramification premise
(star (w i))*(w i) = 1 if P i else 0,
the vertex's conjugate diagonal operator multiplies back to the Haar
unramified projection. This is exact and independent of zero locations.

The identification of this predicate with p not dividing the conductor,
the local Haar integral, the analytic Weil formula, and GRH are NOT
formalized in this small abstract algebra module.
-/

namespace GppHaarPrimePartialIsometry

variable {I : Type*}

/-- Character-wise multiplication by an Euler coefficient. -/
def vertex (w : I → ℂ) (f : I → ℂ) : I → ℂ :=
  fun i => w i * f i

/-- Fourier-side description of averaging over local p-adic units. -/
noncomputable def haarProjector (unramified : I → Prop) (f : I → ℂ) : I → ℂ := by
  classical
  exact fun i => if unramified i then f i else 0

theorem haar_projector_idempotent (P : I → Prop) (f : I → ℂ) :
    haarProjector P (haarProjector P f) = haarProjector P f := by
  classical
  funext i
  by_cases hi : P i <;> simp [haarProjector, hi]

/-- Different prime diagonal vertices commute on every character sector. -/
theorem vertices_commute (w z : I → ℂ) (f : I → ℂ) :
    vertex w (vertex z f) = vertex z (vertex w f) := by
  funext i
  change w i * (z i * f i) = z i * (w i * f i)
  ring

/-- Multiplicativity of Euler coefficients is exactly vertex composition. -/
theorem vertex_product (w z : I → ℂ) (f : I → ℂ) :
    vertex w (vertex z f) = vertex (fun i => w i * z i) f := by
  funext i
  simp [vertex, mul_assoc]

/-- Phase and ramification condition for a primitive Dirichlet character. -/
def phaseCondition (w : I → ℂ) (P : I → Prop) : Prop := by
  classical
  exact ∀ i, star (w i) * w i = if P i then 1 else 0

/-- Exact normal partial-isometry identity V* V = Haar-unramified projection,
written without choosing a matrix or a finite conductor. -/
theorem adjoint_vertex_comp (w : I → ℂ) (P : I → Prop)
    (hw : phaseCondition w P) (f : I → ℂ) :
    vertex (fun i => star (w i)) (vertex w f) = haarProjector P f := by
  classical
  funext i
  change star (w i) * (w i * f i) = if P i then f i else 0
  rw [← mul_assoc, hw i]
  by_cases hi : P i <;> simp [hi]

/-- Since the Fourier coefficient algebra is commutative, V V* = P also. -/
theorem vertex_adjoint_comp (w : I → ℂ) (P : I → Prop)
    (hw : phaseCondition w P) (f : I → ℂ) :
    vertex w (vertex (fun i => star (w i)) f) = haarProjector P f := by
  rw [vertices_commute]
  exact adjoint_vertex_comp w P hw f

/-- The prime vertex commutes with local unramified Haar averaging. -/
theorem vertex_haar_commute (w : I → ℂ) (P : I → Prop) (f : I → ℂ) :
    vertex w (haarProjector P f) = haarProjector P (vertex w f) := by
  classical
  funext i
  by_cases hi : P i <;> simp [vertex, haarProjector, hi]

/-- At a ramified character with w_i=0, the p-Euler vertex annihilates
that character component rather than multiplying by a unit phase. -/
theorem ramified_euler_zero (w : I → ℂ) (f : I → ℂ) (i : I)
    (hw : w i = 0) : vertex w f i = 0 := by
  simp [vertex, hw]

end GppHaarPrimePartialIsometry
