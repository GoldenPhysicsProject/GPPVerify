import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Gram positivity is free — and exactly where Yakaboylu's argument leaves it (eq. 42–58)

Yakaboylu (arXiv:2408.15135v15) constructs `V̂ := ∫₀^∞ ω(t)⁻² |t⟩⟨t| dt` (eq. 42) and notes
it is positive definite on its natural form domain since `ω(t) > 0` — an honest, free fact:
`V̂` is literally multiplication by a positive function. This file records the general
principle behind that freeness, so the real difficulty in Theorem 5.1 can be located
precisely rather than gestured at.

**The free direction.** For *any* positive sesquilinear form and *any* finite family of
vectors drawn from its actual domain — orthogonal or not, this repo's Thread D already
covers the "orthogonal-projection" case implicitly, but the point holds with no
orthogonality at all — the Gram matrix of that family is automatically positive
semidefinite. `theorem gram_posSemidef` below is the completely general Hilbert-space
statement: no oblique-projection machinery is needed to get a PSD Gram matrix from a
positive form, provided the vectors are honestly IN the space the form is defined on.

**Why that does not settle Theorem 5.1.** Yakaboylu's `Ψ_λ` (the actual candidate
eigenstates, indexed by the zeros `λ ∈ Z_Λ`) are *not* in the natural domain where `V̂` is
this cheaply positive: Remark 4.2 (eq. 48) computes `⟨Ψ_λ|V̂|Ψ_λ'⟩ = ∫₀^∞ t^{λ̄+λ'−2} dt`,
which diverges for generic λ, λ'. The regularized `V̂_{R,ε}` (eq. 49) is introduced
*precisely* to assign a finite value to this otherwise-undefined pairing, and its ε → 0
matrix elements (eq. 52–53) are shown to equal `δ_{λ̄+λ'=1}` — i.e. exactly the paired form
of `WeilPositivityCriterion.lean`, whose positivity is already known (Thread D, this repo)
to be equivalent to `Re(λ) = 1/2` for every λ in play. `gram_posSemidef` cannot be invoked
here because its hypothesis — the vectors live in the actual space the form is positive
on — is exactly the thing Remark 4.2 shows fails. The honest remaining content of
Theorem 5.1 is therefore not "does compression preserve positivity" in general (it does,
for real domain vectors, unconditionally, by the lemma below) but specifically: does the
ε → 0 distributional limit at these non-domain, generalized eigenvectors inherit
positivity from the positivity of `V̂_{R,ε}` at finite ε? That limit-transfer is *not*
covered by any general Hilbert-space theorem — it is exactly as hard as, and not
obviously distinct from, `Re(ρ) = 1/2` itself.
-/

namespace GppYakaboylu

open scoped ComplexConjugate BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Gram positivity is free for honest domain vectors.** For any finite index set `S`,
    any vectors `v : ι → V` actually living in the inner product space `V`, and any
    coefficients `c : ι → ℂ`, the Gram-type quadratic form built from `⟪v i, v j⟫` has
    nonnegative real part. No orthogonality of the `v i` is assumed or needed: this is
    exactly `⟪x, x⟫.re ≥ 0` for `x := ∑ i ∈ S, c i • v i`, unpacked by sesquilinearity. -/
theorem gram_posSemidef {ι : Type*} (S : Finset ι) (v : ι → V) (c : ι → ℂ) :
    0 ≤ (∑ i ∈ S, ∑ j ∈ S, conj (c i) * c j * (inner ℂ (v i) (v j) : ℂ)).re := by
  have hx : (inner ℂ (∑ i ∈ S, c i • v i) (∑ j ∈ S, c j • v j) : ℂ)
      = ∑ i ∈ S, ∑ j ∈ S, conj (c i) * c j * (inner ℂ (v i) (v j) : ℂ) := by
    rw [sum_inner]
    simp only [inner_smul_left, inner_sum, inner_smul_right]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  rw [← hx]
  exact inner_self_nonneg (𝕜 := ℂ)

end GppYakaboylu
