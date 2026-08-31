import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Perfect self-duality of Gr(k,n)

Source: ONON5213.tex, Chapter 7 ("The Isomorphism: From Quantum Gravity to Number Theory"),
Theorem "Perfect self-duality of Gr(k,n)": the orthogonal-complement map
`Λ ↦ Λ^⊥` sends `Gr(k,n)` to `Gr(n-k,n)`, is an involution, and restricts to a
self-map of the *same* Grassmannian `Gr(k,n)` iff `n = 2k` — the case relevant to
the paper's `Gr(2,4)`.

This is genuinely elementary finite-dimensional linear algebra (no scheme theory
needed), and Mathlib already has both ingredients: `Submodule.orthogonal_orthogonal`
(the involution property, for submodules with an orthogonal projection -- automatic
in finite dimension) and `Submodule.finrank_add_finrank_orthogonal` (the dimension
count). We assemble them into the paper's exact statement.
-/

namespace GppCelestialHolography

open Module

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The orthogonal-complement map `Λ ↦ Λ^⊥` sends a `k`-dimensional subspace of an
`n`-dimensional inner product space to an `(n-k)`-dimensional subspace: it maps
`Gr(k,n)` into `Gr(n-k,n)`. -/
theorem grassmannian_orthogonal_dim (K : Submodule 𝕜 E) :
    finrank 𝕜 Kᗮ = finrank 𝕜 E - finrank 𝕜 K := by
  have h := Submodule.finrank_add_finrank_orthogonal K
  omega

/-- The orthogonal-complement map is an involution: `(Λ^⊥)^⊥ = Λ`. -/
theorem grassmannian_orthogonal_involutive (K : Submodule 𝕜 E) : Kᗮᗮ = K :=
  Submodule.orthogonal_orthogonal K

/-- **Perfect self-duality of Gr(k,n)** (ONON5213.tex, Ch. 7). The orthogonal-complement
involution restricts to a self-map of `Gr(k,n)` -- i.e. sends a `k`-dimensional subspace
to another `k`-dimensional subspace, rather than merely landing in `Gr(n-k,n)` -- if and
only if `n = 2k`. In particular this is why `Gr(2,4)` (`k = 2`, `n = 4`) is self-dual:
`4 = 2 * 2`. -/
theorem grassmannian_self_dual_iff {k : ℕ} (K : Submodule 𝕜 E) (hK : finrank 𝕜 K = k) :
    finrank 𝕜 Kᗮ = k ↔ finrank 𝕜 E = 2 * k := by
  have h := Submodule.finrank_add_finrank_orthogonal K
  rw [hK] at h
  omega

/-- Specialization to the paper's own case: `Gr(2,4)` is self-dual under orthogonal
complement, since `4 = 2 * 2`. -/
theorem gr_two_four_self_dual
    {k : ℕ} (hk : k = 2) (K : Submodule 𝕜 E) (hK : finrank 𝕜 K = k)
    (hE : finrank 𝕜 E = 4) : finrank 𝕜 Kᗮ = k := by
  have := (grassmannian_self_dual_iff K hK).mpr (by rw [hE, hk])
  exact this

/-- **Gaussian binomial point count for Gr(2,4)** (ONON5213.tex, Ch. 7, `eq:point-count`):
the number of points of `Gr(2,4)` over 𝔽_q is `\binom{4}{2}_q = 1+q+2q^2+q^3+q^4`. We record
the algebraic identity behind this (as a statement over any field, for `q ≠ ±1` so both
denominators are nonzero): `(q^4-1)(q^3-1) / ((q^2-1)(q-1)) = 1+q+2q^2+q^3+q^4`. -/
theorem grassmannian_gaussian_binomial_two_four {q : ℝ} (hq1 : q ≠ 1) (hqm1 : q ≠ -1) :
    (q ^ 4 - 1) * (q ^ 3 - 1) / ((q ^ 2 - 1) * (q - 1)) = 1 + q + 2 * q ^ 2 + q ^ 3 + q ^ 4 := by
  have h1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  have h2 : q + 1 ≠ 0 := fun h => hqm1 (by linarith)
  have h3 : q ^ 2 - 1 ≠ 0 := by
    have hfact : q ^ 2 - 1 = (q - 1) * (q + 1) := by ring
    rw [hfact]; exact mul_ne_zero h1 h2
  rw [div_eq_iff (mul_ne_zero h3 h1)]
  ring

end GppCelestialHolography
