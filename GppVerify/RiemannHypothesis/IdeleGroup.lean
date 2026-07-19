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

## Step 2: the idele group is a topological group, for free

`Units.instTopologicalSpaceUnits` gives every `Mˣ` the topology induced by
`u ↦ (u, u⁻¹) : Mˣ → M × M` (the standard trick that makes inversion continuous), for
any topological monoid `M`; `Units.instIsTopologicalGroupOfContinuousMul` then upgrades
this to a genuine `IsTopologicalGroup Mˣ` whenever `M` has `ContinuousMul`. Since
`AdeleRing R K` already carries `TopologicalSpace` and `IsTopologicalRing` instances
(hence `ContinuousMul`) in Mathlib, `RationalIdeleGroup` is a topological group by pure
instance resolution — no new proof content, but a genuine and necessary upgrade from
"bare group" to "topological group" before compactness/discreteness can even be stated.

## What this does NOT do — the honest current wall

This is still a first step, not the idele class group itself. The next milestone —
local compactness of the idele group — needs compactness of the local unit groups
`𝒪ᵥˣ` at almost every place, and Mathlib's general `RestrictedProduct` group theorem
(`RestrictedProduct.locallyCompactSpace_of_group`) supplies local compactness for
free *given* that ingredient. That ingredient is where the real remaining difficulty
sits: Mathlib proves `PadicInt.compactSpace : CompactSpace ℤ_[p]` for the *concrete*
p-adic integers, but the `FiniteAdeleRing`'s local pieces are built from the *general*
Dedekind-domain machinery (`IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers`),
and no bridge lemma identifying the two for `R = ℤ, K = ℚ` was found in this session's
search (which does not prove none exists — only that it wasn't located). Building that
bridge, or reproving compactness directly for the general `adicCompletionIntegers`, is
the next real undertaking. Beyond that: discreteness of `ℚˣ`, finiteness of the class
number / compactness of the norm-one idele class group (Fujisaki's lemma), the
self-dual Haar measure, and Meyer's spectral construction on top of all of it. Each
remains open.
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

/-- **The idele group of `ℚ` is a topological group.** Free from Mathlib's generic
`Units.instTopologicalSpaceUnits` (the topology making `u ↦ (u, u⁻¹)` an embedding) and
`Units.instIsTopologicalGroupOfContinuousMul` (any topological monoid with continuous
multiplication has a topological-group unit group), applied to the adele ring's own
`TopologicalSpace`/`IsTopologicalRing` instances. No new proof content — but a genuine
and necessary step: `RationalIdeleGroup` is no longer just an abstract group, it carries
the topology that the (still open) local-compactness and discreteness statements need
to be stated against. -/
instance : IsTopologicalGroup RationalIdeleGroup := inferInstance

end GppRH
