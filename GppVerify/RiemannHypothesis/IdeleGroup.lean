import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact

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

## Step 3: the Subring bridge lemma (New)

The earlier pass on this file recorded a wall: Mathlib's local-compactness criterion
`Valued.integer.properSpace_iff_compactSpace_integer` is stated for the generic
`Subring`-typed `Valued.integer K`, but `adicCompletionIntegers` — the object actually
built by the Dedekind-domain machinery `FiniteAdeleRing` uses — has type
`ValuationSubring (adicCompletion K v)`, and no identification between the two was
found. `adicCompletionIntegers_toSubring_eq_integer` closes exactly that gap: both
sides are, by their own defining membership lemmas (`ValuationSubring.mem_toSubring`,
`IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers`, and
`Valuation.mem_integer_iff`), the same set `{x | Valued.v x ≤ 1}`, so a `Subring`
extensionality argument identifies them directly — no deep content, but a genuine
missing link.

## What this still does NOT do — the honest current wall

This closes the *Subring identification* half of the compactness bridge, but not the
compactness statement itself. `Valued.integer.properSpace_iff_compactSpace_integer`
additionally requires a `[Valued.v.RankOne]` instance (the valuation's value group
embeds order-preservingly into `ℝ≥0`, nontrivially). The adic valuation's value group
is `WithZero (Multiplicative ℤ)` (`ℤₘ₀`), and this session's search found no generic
`RankOne` instance for it in Mathlib (`Mathlib.RingTheory.Valuation.RankOne` has the
class definition and its basic API, but no instance keyed to `ℤₘ₀` specifically) — so
constructing that instance (an explicit strictly monotone `ℤₘ₀ →*₀ ℝ≥0`, e.g. via
`n ↦ Real.exp (-n)` on the `Multiplicative ℤ` part, plus the nontriviality proof) is
the next concrete undertaking, not glossed over. Beyond that: discreteness of `ℚˣ`,
finiteness of the class number / compactness of the norm-one idele class group
(Fujisaki's lemma), the self-dual Haar measure, and Meyer's spectral construction on
top of all of it. Each remains open.
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

/-- **Bridge lemma.** The `ValuationSubring`-typed local ring of integers built by the
general Dedekind-domain adic-completion machinery equals, as a `Subring`, the
`Valued.integer` that Mathlib's local field/compactness criteria
(`Valued.integer.properSpace_iff_compactSpace_integer` and its variants) are stated
for. Both sides are the set `{x | Valued.v x ≤ 1}` by their own defining membership
lemmas, so this is a direct `Subring` extensionality argument, not new mathematical
content — but it identifies two previously-unlinked objects, closing the gap the
earlier version of this file recorded as unresolved. -/
theorem adicCompletionIntegers_toSubring_eq_integer
    {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R) :
    (v.adicCompletionIntegers K).toSubring = Valued.integer (v.adicCompletion K) := by
  ext x
  simp only [ValuationSubring.mem_toSubring, Valued.integer, Valuation.mem_integer_iff]
  exact IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K v

end GppRH
