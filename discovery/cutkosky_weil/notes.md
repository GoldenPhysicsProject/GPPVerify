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

**Not formalized in Lean this round**: the two-sided `HasSum` over all of `ℤ` (i.e. the
untruncated `K_r(θ) = Σ_{n∈ℤ} r^{|n|}e^{inθ}` and `K_r-1`'s series) and the `N→∞` limit
passage from `KrN0` to `K_p-1` by continuity; the exact Fourier pair
`H(t) ↔ G(x) = 3/(512π)sech⁴(x/4)` under the convention `G(x) = (1/2π)∫H(t)e^{itx}dt`
(confirmed numerically to ~1e-51 relative error); the removable-singularity/pole-
cancellation claim at `t=±i/2` (confirmed numerically via a shrinking-perturbation
sequence); the full infinite-dimensional Hilbert-space operator packaging
`P_0 C_K P_0 = C_{K-1} = (AP_0)^*(AP_0)` stated in the section above (Mathlib has no ready
`L²(circle)` convolution-operator framework — the finite Gram-square theorem is the
rigorous content that operator identity is standing in for, and is what's actually
proved).

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
