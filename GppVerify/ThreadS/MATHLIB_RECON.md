# Thread S — pinned Mathlib reconnaissance

Step 2 of the Thread S brief. Everything below was found by reading pinned source at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (Mathlib v4.19.0, GPPVerify's own pin) directly
— not loogle, not the Anthropic repo's newer pin (`51e6992e`, Lean v4.33.0-rc2). The two
pins are ~14 months apart; nothing here is assumed to transfer without re-checking.

## What exists

**`Mathlib/LinearAlgebra/Matrix/Spectrum.lean`** (`namespace Matrix.IsHermitian`,
`[DecidableEq n]`):
- `eigenvalues : n → ℝ` — **indexed directly by `n`, the matrix's own index type** (not a
  separate `Fin (Fintype.card n)` — that's `eigenvalues₀`, which `eigenvalues` is built
  from via `Fintype.equivOfCardEq`). This matters: it means `nPos + nNeg + nZero =
  Fintype.card n` reduces to partitioning `Finset.univ : Finset n` by the sign of
  `hA.eigenvalues i`, with no extra reindexing lemma needed.
- `eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)` — an orthonormal
  eigenbasis, canonically indexed by `n` as well.
- `mulVec_eigenvectorBasis`, `spectral_theorem`, `eigenvalues_eq`, `det_eq_prod_eigenvalues`.
- Built from the linear-map spectral theorem
  (`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`), which is where the real
  analytic content lives; the matrix-facing API is a thin wrapper — exactly the situation
  the brief anticipated ("If Mathlib's cleanest formalism is self-adjoint operators rather
  than `Matrix.IsHermitian.eigenvalues`, ... expose a clean Matrix-facing wrapper").
  **Verdict: use `Matrix.IsHermitian.eigenvalues` directly as the Matrix-facing API; it
  already wraps the operator-level theorem, no bridge file needed.**

**`Mathlib/LinearAlgebra/Matrix/PosDef.lean`**: `Matrix.PosSemidef`, `Matrix.PosDef`,
`PosDef.toQuadraticForm'` and `posDef_toMatrix'` — a two-way bridge between real matrices
and `QuadraticForm ℝ (n → ℝ)`. `PosDef.isHermitian`, `PosSemidef.isHermitian` connect back
to `IsHermitian`. Already used elsewhere in this repo
(`QuantumInformation/HalfFlipMatrix.lean` cites `Mathlib`'s `PosSemidef`), so this is a
proven-workable dependency, not a speculative one.

**`Mathlib/LinearAlgebra/QuadraticForm/Real.lean`**: **Sylvester's law of inertia does
exist at the pin**, but only for *real* quadratic forms on a general module
`M : Type*` `[Module ℝ M]`:
- `equivalent_one_neg_one_weighted_sum_squared` — a nondegenerate real quadratic form is
  equivalent to a `±1`-weighted sum of squares.
- `equivalent_signType_weighted_sum_squared`, `equivalent_one_zero_neg_one_weighted_sum_squared`
  — the degenerate case, weights in `SignType` (i.e. `{-1,0,1}`), which is precisely the
  inertia triple `(nPos, nNeg, nZero)` in disguise.

This is real infrastructure and should be used rather than re-derived where possible — but
it is stated for *real* quadratic forms, not directly for *complex Hermitian* matrices. A
complex Hermitian form `v ↦ (v* A v).re` restricted to the underlying real vector space
(realification of `ℂⁿ`) **is** a real quadratic form, so there is a genuine bridge to
build, but it is a bridge to an *existing* Sylvester theorem, not a from-scratch
reconstruction of Sylvester's law itself. This changes the shape of Step 5's work:
the congruence-invariance statement likely factors through this real-quadratic-form
Sylvester theorem rather than needing an independent proof from the spectral theorem.

**`Mathlib/Data/Matrix/Rank.lean`**: `Matrix.rank`, standard rank-nullity content
(`Matrix.rank_eq_finrank_range_toLin'`-style lemmas expected; not exhaustively enumerated
here — sufficient for `Step 3` finite-rank bookkeeping, ordinary linear algebra, low risk).

## What is confirmed absent

Direct search (`grep -rln "Sylvester\|inertia\|Congruent"`) turns up **no** declaration
anywhere in the pinned tree for:
- A named "inertia" concept for **Hermitian** (as opposed to real) forms/matrices.
- A "congruence" relation on Hermitian or symmetric matrices (`Mathlib/Topology/MetricSpace/
  Congruence.lean` is Euclidean-geometry congruence — unrelated; `RamificationInertia/*` is
  number-theoretic ramification — unrelated. Both were checked and ruled out, not assumed
  absent from the grep alone.)
- Any "signature" notion for matrices (only `SignType`-weighted sums in the real
  `QuadraticForm` file above, which is the closest analogue).

**Per the brief's explicit instruction, this is not routed around with an opaque
hypothesis: Sylvester-type congruence invariance for the Hermitian case must be built
locally in `SignatureInertia.lean`, using the real-quadratic-form Sylvester theorem above
as the base case reached via realification, or directly from
`Matrix.IsHermitian.eigenvalues` + `eigenvectorBasis` if that route proves cleaner once
attempted.**

## Representation chosen, and why

**Chosen: `Matrix.IsHermitian.eigenvalues : n → ℝ`, counting `nPos/nNeg/nZero` as
`Finset.card` of `Finset.univ.filter` by sign.**

Alternatives considered:
- *Self-adjoint operator on `EuclideanSpace`, bypassing `Matrix` entirely.* Rejected as the
  primary representation: the brief explicitly asks for a clean Matrix-facing wrapper for
  downstream files (Step 4's bridge to `WeilPositivityCriterion.lean`, which works with
  matrices/Gram forms, not abstract operators), and `Matrix.IsHermitian.eigenvalues`
  already *is* that wrapper — building a second one would duplicate Mathlib's own design.
- *Route inertia entirely through the real `QuadraticForm` Sylvester theorem, skipping
  eigenvalues.* Rejected as the *primary* definition (though it will likely appear as a
  proof technique for congruence invariance, Step 5): defining `nPos/nNeg/nZero` via
  eigenvalue sign is the standard, checkable definition matching the paper's own usage
  (`n₊(Q)`, trace and Hilbert–Schmidt norm all quoted eigenvalue-wise), and it makes
  `inertia_sum` nearly free (a trichotomy partition), whereas defining inertia via
  "the largest dimension of a subspace on which the form is positive-definite" (the other
  standard equivalent definition, and the one the brief's `dim_le_nPos_of_posDef_on`
  theorem is stated about) would need to be **proved equal** to the eigenvalue count
  regardless of which one is primary — so the eigenvalue definition, being the more
  directly computable one, is primary, and `dim_le_nPos_of_posDef_on` is the theorem that
  connects it to the subspace-dimension characterization the brief also wants.

## Local lemmas genuinely required (not found upstream)

1. `inertia_sum` — trichotomy partition of `Finset.univ` by `eigenvalues i`'s sign;
   mechanical given the API above, but not present upstream as a named lemma for
   `IsHermitian.eigenvalues` specifically.
2. `dim_le_nPos_of_posDef_on` / `dim_le_nNeg_of_negDef_on` — the subspace-dimension bound;
   this is the standard "a positive-definite subspace has dimension at most the number of
   positive eigenvalues" fact, provable via the eigenvector basis but not present as a
   named Mathlib lemma at the pin.
3. `CongruentHermitian` (definition) and `inertia_congruent` — genuinely absent, as
   confirmed above; the real-`QuadraticForm` Sylvester theorem is the intended base to
   reach it through.
4. The rank–trace inequality itself (paper's Lemma 3.2) — pure finite-dimensional linear
   algebra over the inertia triple, not stated anywhere in Mathlib (searched
   `Mathlib/LinearAlgebra/Matrix/Rank.lean`-adjacent files; nothing of this shape exists).
   This is the single load-bearing lemma identified in `SOURCES.md` and is Thread S's
   actual deliverable, not an assembly of existing pieces.
