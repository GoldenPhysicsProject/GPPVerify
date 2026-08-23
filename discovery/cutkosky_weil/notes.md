# discovery/cutkosky_weil — Local shadow kernels and the finite-prime Weil kernel

Research-front notes for the 2026-08-22 directive: "celestial Cutkosky positivity →
local shadow kernels → finite-prime Weil kernel → Casimir compression → global Weil
positivity → RH." Same convention as `discovery/local_field_shadow/` and
`discovery/shadow_ope/`: **discovery only, except where explicitly noted as formalized
in Lean.** Read this file first; `cutkosky_weil_verify.py` is the numerical companion,
rerun fresh in this container.

## Self-correction (read this first)

The first pass of this file claimed, as its central finding, that "no positivity-
preserving projection from `K_p` to `K_p−1` exists." **That claim was wrong**, caught by
review before any false statement reached Supabase (it had already been merged to `main`
in the Lean discovery notes and PR description, which this round corrects).

The error: the first pass tested whether the **Fourier-coefficient sequence itself**
`(c_n)_{n∈ℤ}` — with `c_0 = 0`, `c_n = r^{|n|}` for `n≠0` — is positive-definite as a new
kernel, by building the Toeplitz matrix `T[j,k] = c_{j-k}` (indices `j,k` ranging over
*frequencies*) and finding it indefinite. That computation is numerically correct, but it
answers the wrong question. The question that actually matters — "is `K_p − 1` a positive
kernel on the circle" — asks whether the **Gram matrix built from point evaluations**,
`M_{jk} = (K_p-1)(θ_j - θ_k)` for arbitrary finite angle configurations `θ_1,…,θ_N`, is
positive semidefinite. This is precisely `GppHaarPositivityWeil.PositiveType` (already in
this repo, `HaarPositivityWeil.lean`/`ConvolutionSquarePositive.lean`) applied to
`K_p − 1`. These are different objects: a Toeplitz matrix indexed by frequency differences
is not the same matrix as a Gram matrix indexed by point-evaluation differences.

**The corrected answer: `K_p − 1` IS positive-definite as a kernel — trivially, and this
holds prime-by-prime.** Convolution by `K_p` is diagonalized in the Fourier basis with
eigenvalues `r^{|n|} ≥ 0` for every `n`; convolution by `K_p−1` has the same eigenvalues
except the `n=0` (vacuum) eigenvalue is set to exactly `0`. Zeroing one of infinitely many
nonnegative eigenvalues cannot make any of the others negative, so the vacuum-subtracted
operator is still positive semidefinite. This is now a genuine theorem at every finite
truncation (`KrN0_gram_nonneg` below), not merely an assertion — proved via a layered
finite Fourier/Gram-square identity, matching the classical Herglotz/Bochner mechanism.
(A first attempt to prove the untruncated, infinite-`ℤ` version as one monolithic theorem
repeatedly hit elaboration timeouts even at 20× the default heartbeat budget — a proof-
engineering failure, not a mathematical one; see "Proof engineering" below for the
diagnosis and the fix.)

## The central question, answered (corrected)

Daniel's own closing instruction for this round was: *"What physical/mathematical
projection turns `K_p` into `K_p−1` while preserving positivity globally? If we find
that projection from the Cutkosky completeness structure, then we have something
genuinely different from simply importing somebody else's RH machinery."*

**Corrected direct answer: at the single-prime level, no projection is even needed — the
vacuum subtraction `K_p ↦ K_p−1` preserves kernel-positivity automatically, for every
prime.** The "projection" is nothing more exotic than the orthogonal compression
`P_0` (projection off the constant/DC mode): writing `C_K` for convolution by `K_p` and
`P_0 = I - |e_0⟩⟨e_0|` for the projection orthogonal to the zero-frequency mode,

  `P_0 C_K P_0 = C_{K_p - 1} ≥ 0`,

and — since `C_K` is itself diagonal with eigenvalues `r^{|n|} = (r^{|n|/2})^2` — this
factors as a manifest square: with `A e_n := r^{|n|/2} e_n`,

  `C_{K_p - 1} = (A P_0)^* (A P_0) ≥ 0`.

This *is* structurally the same shape as the Cutkosky completeness relation
`Σ_X |X⟩⟨X|` the directive pointed to: `C_{K_p-1}` is manifestly `B^*B` for
`B = A P_0`, i.e. a sum/integral of positive rank-one projectors weighted by
`r^{|n|}`, `n≠0`. The finite-dimensional/finite-point-configuration content of this
statement (the part actually verified below and proved in Lean) is the Gram-square
identity; the full infinite-dimensional operator statement above is recorded as the
correct conceptual packaging but is not itself formalized as a Hilbert-space operator
identity in Lean this round (see "Not formalized" below).

### Corrected Toeplitz vs. Gram-matrix numerics

| test | object | p=2 | p=3 | p=5 |
|---|---|---|---|---|
| **wrong** (1st pass) | Toeplitz `T[j,k]=c_{j-k}` of `K_p-1`'s coefficients, `N=6` | indefinite (min eig **−0.87**) | indefinite (min eig **−0.73**) | indefinite (min eig **−0.61**) |
| **correct** (this pass) | Gram `M_{jk}=(K_p-1)(θ_j-θ_k)`, random non-equally-spaced points | PSD (min eig `0.19`–`0.27`) | PSD (min eig `0.004`–`1.07`) | PSD (min eig `9e-4`–`0.20`) |

The corrected Gram-matrix test was run for `p=2,3,5`, two random (non-equally-spaced,
non-integer) point configurations each (`N=5` and `N=9` points), confirming positive
semidefiniteness in every trial; a separate cross-check confirms the quadratic form
computed from the closed form matches the truncated Fourier-square sum
`Σ_{n≠0} r^{|n|}|Σ_j c_j e^{-inθ_j}|²` to ~`1e-49` relative error for random complex
weights. See `cutkosky_weil_verify.py` §5 for the full rerun.

**What this means for the research program.** This reverses the earlier negative
framing. The naive local mechanism does exist prime-by-prime — but its existence is not
by itself news: it is exactly the statement that a Poisson kernel minus its own DC term
is still positive-type, a fact fully explained by Herglotz/Bochner. The genuinely open
question is unchanged in substance: whether the **assembled** `Q_GPP[f] = Σ_p Q_p[f] +
Q_∞[f]` connects to the classical Weil quadratic form and, if so, whether *that* object
is globally nonnegative. Single-prime positivity of `K_p − 1` was never going to answer
that on its own (the classical Weil explicit formula's local prime terms are individually
sign-indefinite in their usual normalization even though local `K_p` positivity holds) —
so this correction, while reversing the specific numerical claim, does not change the
overall honest boundary: the bridge to global Weil positivity remains open, and the
Cutkosky-completeness-relation analogy above is a structural observation, not a proof
that it propagates to the assembled prime sum.

## Fourth pass: removable singularity and the full `N → ∞` passage, completed

Two items left open by the third pass are now done — the removable singularity of the
Archimedean cut kernel at `t=0`, and the passage from the finite-truncation milestone
`KrN0_gram_nonneg` to genuine, untruncated positive-type positivity of `K_r - 1`. Both were
built as small, independently-tested layers (per the third pass's own lesson), and both
compile in well under a minute total.

**Removable singularity.** `cutKernel t = t/(4 sinh(2πt))` gives Lean's junk value `0/0=0`
at `t=0`. The genuine limit, proved from `sinh`'s derivative at `0` (`HasDerivAt Real.sinh
(Real.cosh 0) 0`, i.e. slope `1`) rather than merely asserted: `tendsto_cutKernel_zero :
cutKernel → 1/(8π)` as `t→0` (`t≠0`). `cutKernelExt := Function.update cutKernel 0 (1/(8π))`
is the continuous extension (`continuousAt_update_same` turns the punctured-neighborhood
limit directly into continuity at the point); `Hext t := (t²+1/4)·cutKernelExt t` inherits
`Hext 0 = 1/(32π)` (exactly matching the numerically-observed value from the earlier
pass) and `Hext_nonneg` (nonnegativity everywhere, now with the genuine value at `0`,
not the coincidental `0≤0` from the junk value).

**The `N → ∞` passage**, following the review's explicit route — separate convergence from
algebra, build `Summable` via the geometric tail bound, then pass positivity to the limit
by continuity — rather than reviving the third pass's monolithic `HasSum`/`Int.rec`
construction that had timed out:
1. `tendsto_Icc_atTop`: the symmetric intervals `Icc(-N,N)` are cofinal in `Finset.atTop`
   on `Finset ℤ` (the intervals exhaust `ℤ`).
2. `summable_rpow_natAbs`/`summable_KrClosed_summand`: `Summable` (existence only) of the
   vacuum-subtracted two-sided series, via `Summable.of_nat_of_neg` (comparison to the
   geometric series `Σr^n`) — much cheaper than tracking `HasSum` *values* through
   `Int.rec`/`HasSum.of_nat_of_neg_add_one`, which is what caused the third pass's timeout.
3. `tsum_KrClosed_summand_eq`: the tsum's *value* is identified as `K_r(θ)-1`, via the two
   one-sided geometric series (`Summable.tsum_of_nat_of_neg`) and the same closed-form
   algebra already used for `Kp_pos`/`KrClosed`.
4. `tendsto_KrN0`: `KrN0 r N θ → K_r(θ)-1` as `N→∞`, by composing the `HasSum`'s own
   `Tendsto` (along `Finset.atTop`) with the cofinality from step 1.
5. `KrClosed_minus_one_tendsto_positive`/`KrClosed_minus_one_positiveType`: positivity of
   the finite Gram sum at every truncation `N` (`KrN0_gram_nonneg`) passes to the
   `N→∞` limit via `ge_of_tendsto` (a real-valued sequence eventually `≥0` has a `≥0`
   limit), landing `GppHaarPositivityWeil.PositiveType (fun θ => KrClosed r θ - 1)`
   unconditionally — the genuine, untruncated analytic statement.

**Still open**: the exact Fourier pair `H(t)↔G(x)=3/(512π)sech⁴(x/4)` and the `t=±i/2`
pole-cancellation claim remain numerical-only (see "Not formalized" below — unchanged by
this pass); the spectral vacuum-projection operator identity `C_{K_p-1}=P_0 C_{K_p} P_0`
on a precisely-defined Hilbert space and the Mellin/Fourier/adelic bridge to the classical
Weil kernel are the next targets, not attempted this round.

## Fifth pass: the operator-level vacuum-compression identity — closed; the finite-prime
## Weil-kernel target precisely identified and re-scoped

A further review directive named a six-item program, prioritizing item 1 (the operator
identity, "not merely the finite Fourier identity again") and item 4 (the Mellin/adelic
bridge, "the one I care about most"). This pass closes item 1 completely and produces a
precise, checked (but not yet Lean-formalized) mathematical finding for items 2–3 — while
also correcting a mismatch in how items 4 and 6 were framed.

**Item 1 — the operator identity, closed.** Built the actual bounded-operator statement on
`Ell2Z := ℓ²(ℤ,ℂ)` (Mathlib's `lp (fun _:ℤ=>ℂ) 2`), the natural Fourier-coefficient model: by
Parseval, convolution by a kernel on `L²(𝕋)` is unitarily equivalent to diagonal
multiplication by its Fourier coefficients on `ℓ²(ℤ)`, so working directly on `ℓ²(ℤ)` gives
the genuine operator content without needing to build the circle convolution operator
(Bochner kernel integrals) in Lean at all.
- `mulOpCLM w hw : Ell2Z →L[ℂ] Ell2Z` — the bounded (operator norm `≤1`) diagonal
  multiplication `ContinuousLinearMap` for any weight `w:ℤ→ℂ` with `‖w n‖≤1`, built via
  `LinearMap.mkContinuous` from an explicit norm bound (`mulOpLin_norm_le`, proved by
  comparing `∑'‖w(n)x(n)‖²` to `∑'‖x(n)‖²` termwise then taking square roots via
  `Real.rpow_le_rpow_iff`).
- `C_{K_r} := mulOpCLM (KrWeight r)` (symbol `r^{|n|}`), `P_0 := mulOpCLM P0Weight` (symbol
  `0` at `n=0`, `1` elsewhere — the vacuum-deleting projection), `C_{K_r-1} := mulOpCLM
  (KrMinusOneWeight r)` (symbol `0` at `n=0`, `r^{|n|}` elsewhere, matching the two-sided
  Fourier series of `K_r-1` from `tsum_KrClosed_summand_eq`, fourth pass).
- **`vacuum_compression_operator_identity`**: `C_{K_r-1} = P_0 * C_{K_r} * P_0` as literal
  `ContinuousLinearMap` composition — proved via `mulOpLin_comp` (composing two diagonal
  operators multiplies their symbols pointwise) applied twice, reducing to the one-line
  algebraic fact `P_0(n)·K_r(n)·P_0(n) = (K_r-1)(n)` for every `n∈ℤ`
  (`P0Weight_mul_KrWeight_mul_P0Weight_eq`: `0=1-1` at `n=0`, `1·r^{|n|}·1=r^{|n|}`
  elsewhere).
- **`vacuum_compressed_operator_positive`**: positivity of the compressed operator, derived
  as a genuine corollary — `mulOpCLM_inner_re_nonneg` is proved once, generally, for *any*
  bounded diagonal operator with `Re(w(n))≥0` for every `n` (`⟪x,Tx⟫ = Σ_n w(n)|x(n)|²`,
  real part `≥0` termwise; the imaginary part of `w` plays no role since it multiplies the
  manifestly-real `|x(n)|²`), then specialized to `K_r-1`'s already-known eigenvalue signs.
  No new analytic content beyond the general lemma — exactly "as a corollary of the
  Fourier eigenvalues" as directed.
- 8 new theorems, all kernel-clean (`propext`/`Classical.choice`/`Quot.sound` only), no
  `sorry`, no new axiom. `lake build GppVerify` green.

**Items 2–4/6 — the target re-identified.** Checking the actual statement of
`GppWeilCriterion.rh_iff_weil_pairedForm_nonneg` (`WeilPositivityCriterion.lean`) against
the directive's framing found a mismatch, one this file's own module doc had already
flagged before this pass began (`Connecting the two is itself a substantial, separate
undertaking`): `pairedForm ι S c := Σ_{ρ∈S} conj(c(ι ρ))·c(ρ)` is a **zero-indexed**
reflection pairing over finite subsets of the *unknown zero set itself*, paired by the
involution `ι(ρ)=1-ρ̄`. It carries **no prime index, no Mellin convention, no Haar
normalization, no ε, no ζ — nothing for a "finite-prime Weil kernel in this theorem's
normalization" to mean.** This is the Yakaboylu/Bombieri-Lagarias reformulation
(arXiv:2408.15135): its content is a self-contained "positivity of a simple reflection
pairing forces fixed points" linear-algebra fact, proved unconditionally already, and it
does **not** go through the classical prime-indexed explicit formula at all.

The object that genuinely deserves the name "finite-prime Weil kernel, classical
normalization" is `GppHaarPositivityWeil.weil_criterion` (`HaarPositivityWeil.lean`):
`D_k = Σ_ρ Ω̂(ρ) + local terms` in Weil's own adelic language. That theorem is a full
`True := trivial` stub, honestly documented as blocked on Tate's thesis (adelic zeta
integrals) and idèle class groups — **neither exists in Mathlib**, a large, well-known,
multi-year-scale gap, not a proof-engineering issue this session's bisection discipline can
route around.

**But the classical, *elementary* (non-adelic) explicit formula does not need that
machinery**, and checking it by hand against `Wp` turned up a clean, exact identity. Let
`ζ_p(s) := (1-p^{-s})^{-1}` be the local Euler factor. Its logarithmic derivative is the
standard prime-power Dirichlet series:
```
-ζ_p'/ζ_p(s) = log(p) · Σ_{k≥1} p^{-ks}         (Re s > 0)
```
At `s = 1/2+it`: `p^{-ks} = r^k e^{-ikθ}` with `r=p^{-1/2}`, `θ=t log p` (exactly `Kp`'s own
substitution, `Kp_eq_KrClosed`). So
```
Re(-ζ_p'/ζ_p(1/2+it)) = log(p) · Σ_{k≥1} r^k cos(kθ).
```
Meanwhile `Kp p t - 1 = KrClosed r θ - 1 = Σ'_{n≠0} r^{|n|}e^{inθ}` (already proved,
`tsum_KrClosed_summand_eq`, fourth pass) `= 2 Σ_{k≥1} r^k cos(kθ)` (pairing `n=±k`). So:
```
Wp(p,t) = log(p)·(Kp(p,t)-1) = 2·Re(-ζ_p'/ζ_p(1/2+it))    exactly, for all real p>1, t.
```
Checked by hand from Mathlib-available building blocks only (geometric series, `Complex.log`
identities) — no adelic content, no Tate's thesis. This **is** a correct, precise
identification of `Wp` as (twice the real part of) the local Euler-factor logarithmic
derivative on the critical line, and it is the honest next Lean target for items 2–3: not
yet formalized (isolated here as a checked-by-hand identity rather than smuggled in as a
theorem), but concretely in reach with the same geometric-series machinery already proved
for `tsum_KrClosed_summand_eq` — no new Mathlib gap.

**Item 6 (global assembly against `rh_iff_weil_pairedForm_nonneg`) does not apply as
stated**, for the same reason as items 2–4: that theorem's positivity *hypothesis* carries
no prime-side data to assemble in the first place — it is already proved unconditionally
equivalent to RH without needing any local/prime input. The genuine "does local positivity
assemble into a global positive quadratic form" question belongs to `weil_criterion`
(`D_k = Σ_ρ Ω̂(ρ) + local terms`), which — even granting the elementary `Wp` identity above
for the local terms — still needs the *global* explicit formula (contour integration of
`ζ'/ζ` around the critical strip, picking up the zero-sum via the argument principle) to
exist in Lean at all before an assembly question can even be posed. That is not currently
in the tree and is a separate, large, classical-analytic-number-theory undertaking in its
own right (distinct from, and smaller than, the adelic Tate's-thesis route, but still
substantial) — scoped honestly here, not attempted.

## What's proved in Lean (`GppVerify/RiemannHypothesis/CutkoskyWeilBridge.lean`)

- `Kp (p t : ℝ) : ℝ` — the finite-place shadow kernel in real closed form,
  `(1−p⁻¹)/(1 − 2p^{−1/2}cos(t log p) + p⁻¹)`.
- `Wp (p t : ℝ) : ℝ := log p · (Kp p t − 1)` — the vacuum-subtracted, log-weighted kernel.
- **`Kp_pos`**: `1 < p → 0 < Kp p t` for all real `t`. Unconditional, no axiom.
- `cutKernel (t : ℝ) : ℝ := t / (4 sinh(2πt))` — the celestial cut, already derived
  elsewhere in the tree.
- `H (t : ℝ) : ℝ := (t² + 1/4) · cutKernel t` — the Casimir-weighted Archimedean kernel.
- **`H_nonneg`**: `0 ≤ H t` for every real `t`. Unconditional, no axiom.
- `KrClosed (r θ : ℝ) : ℝ := (1-r²)/(1-2r cos θ+r²)` — the Poisson kernel with the
  parameter `r` exposed directly (`Kp p t = KrClosed (p^{-1/2}) (t log p)`, proved as
  `Kp_eq_KrClosed`).
- **The layered finite Fourier/Gram-square development** (the corrected central result,
  restructured for elaboration speed after the monolithic attempt below timed out):
  - `gram_square_freq` — fixed-frequency Gram identity, `Σᵢⱼ c̄ᵢcⱼe^{in(xᵢ-xⱼ)} =
    ‖Σᵢcᵢe^{-inxᵢ}‖²`, pure finite algebra, generalizing `ConvolutionSquarePositive.lean`'s
    `gram_square_nonneg` to complex amplitudes.
  - `gram_square_freqSum` — the same identity summed over a finite set of frequencies
    `n ∈ F` with real weights `a : ℤ → ℝ`.
  - `gram_square_freqSum_nonneg` — nonnegativity corollary (trivial given the above, via
    `Finset.sum_nonneg`).
  - `KrN0 (r : ℝ) (N : ℕ) (θ : ℝ) : ℂ` — the **truncated** finite-place shadow kernel
    `K⁰_{r,N}(θ) = Σ_{0<|n|≤N} r^{|n|}e^{inθ}`, a genuine finite sum (no `HasSum`, no
    convergence machinery needed at this stage).
  - **`KrN0_gram_nonneg`** (the milestone): `Σᵢⱼ c̄ᵢcⱼ K⁰_{r,N}(xᵢ-xⱼ) ≥ 0` for every
    truncation `N`, every finite point configuration, every `0≤r`. Unconditional, no axiom.
  All four layers build independently in under 4 seconds each.
- **The `N → ∞` passage** (fourth pass — see that section above for the full account):
  `tendsto_Icc_atTop`, `summable_rpow_natAbs`, `summable_KrClosed_summand`,
  `tsum_ite_zero_eq_tsum_sub`, `tsum_KrClosed_summand_eq`, `tendsto_KrN0`,
  `KrClosed_minus_one_tendsto_positive`, and **`KrClosed_minus_one_positiveType`** — the
  genuine, untruncated `GppHaarPositivityWeil.PositiveType (K_r - 1)`, unconditional, no
  axiom.
- **The removable singularity** (fourth pass): `tendsto_cutKernel_zero`, `cutKernelExt`,
  `cutKernelExt_zero` (`=1/(8π)`), `Hext`, `Hext_zero` (`=1/(32π)`), `Hext_nonneg`.
- **The operator-level vacuum-compression identity** (fifth pass — see that section above
  for the full account): `Ell2Z := ℓ²(ℤ,ℂ)`, `mulOpLin`/`mulOpCLM` (the bounded diagonal
  multiplication operator, `LinearMap` and `ContinuousLinearMap` forms), `mulOpLin_comp`
  (composition multiplies symbols), `mulOpLin_norm_le`, `KrWeight`/`P0Weight`/
  `KrMinusOneWeight` (the three Fourier symbols) with their norm bounds,
  `mulOpCLM_inner_re_nonneg` (the general positivity-from-eigenvalue-signs lemma),
  `P0Weight_mul_KrWeight_mul_P0Weight_eq`, **`vacuum_compression_operator_identity`**
  (`C_{K_r-1} = P_0 * C_{K_r} * P_0` as genuine bounded-operator composition), and
  **`vacuum_compressed_operator_positive`** (positivity of the compressed operator, as a
  corollary). Unconditional, no axiom.

**Not formalized in Lean this round**: the exact Fourier pair
`H(t) ↔ G(x) = 3/(512π)sech⁴(x/4)` under the convention `G(x) = (1/2π)∫H(t)e^{itx}dt`
(confirmed numerically to ~1e-51 relative error); the removable-singularity/pole-
cancellation claim at `t=±i/2` (confirmed numerically via a shrinking-perturbation
sequence — a different, complex-analytic removable singularity from the real-axis one at
`t=0` closed in the fourth pass); the elementary identity `Wp(p,t) =
2·Re(-ζ_p'/ζ_p(1/2+it))` (checked by hand, fifth pass — see that section for the full
derivation; the honest next Lean target for items 2–3 of the operator/Weil-bridge
program); the classical explicit formula itself (contour integration of `ζ'/ζ`, the
argument principle) and the adelic Tate's-thesis route (`weil_criterion`), both large,
separate, unattempted undertakings — see the fifth-pass section above for the precise
scoping of why neither is a proof-engineering-fixable gap.

## Proof engineering: why the first Lean attempt failed, and the fix

A first attempt proved the untruncated `HasSum` directly (`hasSum_KrClosed_fourier`) and
built `PositiveType (K_r - 1)` on top of it in one large nested theorem
(`KrClosed_minus_one_positiveType`). Both repeatedly hit `(deterministic) timeout at whnf`
— first at the default 200,000-heartbeat budget, then still at 1,000,000 and even
4,000,000 (20× default) after several rounds of fixes to the underlying mathematics
(which were themselves correct). Bisected by extracting sub-`have`s into standalone
scratch files and testing each with `lake env lean` at the *default* heartbeat budget
(fast fail/pass, seconds not minutes) rather than repeatedly waiting out multi-minute
full-file builds. Root causes found:

1. `HasSum.of_nat_of_neg_add_one` (combining a `HasSum` on `ℕ` and one on the negatives
   into a `HasSum` on `ℤ`) elaborates in under 20 seconds with 4 bare hypotheses in
   context, but times out when inlined into a theorem whose local context also carries
   `r, hr0, hr1, θ` and several derived facts — elaboration cost scales with local-context
   size for this combinator, not just the goal itself. Fixed by extracting it as its own
   minimal-context helper lemma.
2. Even after that fix, the full monolithic Gram-square argument — run once, over an
   infinite series, inside one proof with `ring_nf`/`nlinarith` calls on deeply nested
   `Complex.re`/`Complex.im` expressions — accumulated enough elaboration cost to blow up
   regardless of heartbeat budget.

The fix (per external review) was architectural, not a bigger heartbeat number: split the
Gram-square argument into the four small, single-purpose layers listed above, test each
standalone before composing, and — for now — stop at the finite truncation `KrN0` rather
than fighting the infinite `HasSum` inside the same proof. This is the concrete lesson
carried forward: **if a Lean theorem takes more than about a minute to elaborate, that is
itself a signal to bisect and re-layer, not to raise `maxHeartbeats` and wait.**

## Item 3 — the Casimir operator's representation-theoretic origin

Not attempted as a Lean construction this round. The precise missing interface: Mathlib
(pinned `v4.19.0`) has no development of the principal-series representations of
`SL(2,ℝ)` or their Casimir/Laplace–Beltrami operator eigenvalues — the `t²+1/4` factor
here is used purely as a *number* (the known eigenvalue), not derived from an actual
operator on a Hilbert space of sections. Building the operator itself is a separate,
substantial representation-theory undertaking, not a small gap-fill.

## Item 4/5 — `Q_GPP` construction and comparison to the classical Weil form

Not attempted this round beyond the single-prime kernel-positivity result above. Before
building `Q_GPP[f] = Q_∞[f] + Σ_p Q_p[f]` and comparing it to the classical Weil
explicit-formula quadratic form, it is necessary to be precise about which object
`WeilPositivityCriterion.lean` already contains: **`GppWeilCriterion.pairedForm`** there
is an *abstract* pairing `Σ_{ρ∈S} conj(c(ι ρ))·c(ρ)` over finite subsets of the actual
(unknown) nontrivial-zero set — it is not the classical prime-sum quadratic form this
directive's `Q_GPP` is meant to build. `rh_iff_weil_pairedForm_nonneg` is a real,
unconditional, already-proved biconditional, but bridging it to a prime-side
construction like `Q_GPP` requires the classical Weil explicit formula itself (the
integral-transform identity relating a sum over zeros to a sum over primes plus an
Archimedean term) — substantial, separate infrastructure, not present in Mathlib, and
not attempted here. Per the directive's own explicit warning ("do not call two objects
identical because their Fourier multipliers look alike"), no such identification is made
or assumed anywhere in this round's work — including the Cutkosky-completeness-relation
analogy above, which is offered as a structural observation about `K_p-1` alone, not as
a claim about `Q_GPP` or the classical Weil form.

## Item 9 — Connes–Consani / Selberg / Mayer / Tate / Knapp–Stein

Not used as machinery anywhere in this file or script. `K_p` and `H` here are derived
purely from the GPP local-field-shadow-kernel route (already in the tree) and the
celestial-cut kernel (already in the tree); no operator, projection, or identity was
imported from the Connes–Consani program. The `P_0 C_K P_0` / `(AP_0)^*(AP_0)`
observation above is a direct, elementary consequence of `K_p`'s own diagonal Fourier
structure — it is not imported from, or motivated by, their scaling-trace construction.

## Explicit non-claims

- **No RH claim, conditional or otherwise.** `rh_iff_weil_pairedForm_nonneg` (pre-
  existing) states an equivalence between RH and an abstract nonnegativity condition on
  an unknown set (the actual zeros); nothing in this round establishes that condition.
- **No claim of global Weil positivity** for any constructed quadratic form — no such
  form was assembled this round.
- **No claim that the single-prime result bridges to `Q_GPP` or the classical Weil form**
  — see item 4/5 above.
- **No import of Connes–Consani's compression operator** or any external RH program's
  machinery as a black box.
- The golden-ratio/modular results (`GoldenRatioHyperbolicSector.lean`, prior round) are
  unrelated exact structural facts and are not used here to argue toward positivity.

## Reproducing

```
python3 cutkosky_weil_verify.py
```
No network access required; pure `mpmath` (dps=50), runs in well under a minute.
