import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# The idele group of ℚ: first steps

Not paper-sourced — genuine new infrastructure, building on Mathlib's
`NumberField.AdeleRing` (added since the many "idele class groups are not in Mathlib"
notes elsewhere in this repo were written; see `QuartetPerturbation.lean`'s Thread Q).

## What this file does

The idele group `𝔸ₖˣ` of a number field `K` is, by definition, the group of units of its
adele ring. Mathlib's `NumberField.AdeleRing R K` gives a genuine `CommRing`, so `Units`
of it is available for free — no new definition of the *ring* is needed. What is not
free is showing `ℚˣ` genuinely embeds in it: the diagonal embedding `q ↦ (q)ᵥ` of the
idele class group construction `𝔸_ℚˣ / ℚˣ` has to be an *injective* group homomorphism
before the quotient can even be discussed, and this is the first concrete piece of that.

## What this does NOT do

This is a first, modest step, not the idele class group itself. Still missing, each a
separate and substantially harder undertaking: a topology on the idele group making it a
locally compact topological group (needs the `Units` topology via `u ↦ (u, u⁻¹)` and
compactness of the local unit groups `𝒪ᵥˣ` at almost every place — plausible via the
`RestrictedProduct` group theorems already in Mathlib, but not yet wired up here);
discreteness of `ℚˣ` in that topology; finiteness of the class number / compactness of
the norm-one idele class group (Fujisaki's lemma); the self-dual Haar measure; and
Meyer's actual spectral construction on top of all of that. Each remains open.
-/

namespace GppRH

open NumberField

/-- The idele group of `ℚ`: the group of units of the adele ring `𝔸_ℚ = AdeleRing ℤ ℚ`. -/
abbrev RationalIdeleGroup : Type := (AdeleRing ℤ ℚ)ˣ

/-- The diagonal embedding `ℚˣ → 𝔸_ℚˣ` of the rational unit group into the idele group,
induced by the canonical algebra map `ℚ → 𝔸_ℚ`: a nonzero rational `q` maps to the idele
`(q)ᵥ` that is `q` at every place, which is a genuine unit of the adele ring because the
algebra map is a ring homomorphism (so `(q)ᵥ · (q⁻¹)ᵥ = (1)ᵥ = 1`). -/
noncomputable def diagonalEmbedding : ℚˣ →* RationalIdeleGroup :=
  Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom

/-- **The diagonal embedding is injective.** Distinct nonzero rationals give distinct
ideles. This is the group-theoretic prerequisite for the idele class group
`𝔸_ℚˣ / ℚˣ` to make sense as a quotient by a genuine (isomorphic-image) subgroup:
before the much deeper discreteness/compactness content can even be stated, `ℚˣ` has to
actually embed. -/
theorem diagonalEmbedding_injective : Function.Injective diagonalEmbedding :=
  Units.map_injective (NumberField.AdeleRing.algebraMap_injective ℤ ℚ)

end GppRH
