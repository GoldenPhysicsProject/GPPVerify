# Thread S — source acquisition and dependency audit

Step 0 of the Thread S brief. Every claim below was verified against the primary source
text (paper PDF and Lean repository), not against summaries, blog posts, or press
coverage. Search/fetch trail: WebSearch → WebFetch (blog post, failed on the raw paper PDF)
→ `curl` + `pdfminer.six` in an isolated venv (system `cryptography` package is broken in
this container — panics on import — so PDF extraction needed a clean venv) → direct text
read of the extracted paper and Lean-repo README.

## RED-ALERT resolved: which "67.25%" is this, and is it conditional?

**It is unconditional**, and it is a different theorem from arXiv:2501.14545. The two must
not be conflated — they were being conflated in the initial web-search summaries.

- **arXiv:2501.14545** (Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh) proves 2/3 simple,
  2/3 on the critical line, and 1/3 simple-and-critical, but **assumes a narrow vertical-box
  hypothesis**: all zeros with `T < γ ≤ 2T` lie within `b/log T` of the critical line,
  `b → 0`. It is one of the paper's *analytic inputs*, not the source of the headline
  constant.
- **The actual source of "67.25%"** is Claude/Anthropic's August 2026 paper, *"More than
  two thirds of the zeros of the Riemann zeta function are simple and on the critical
  line"* (dated August 11, 2026). Its abstract states plainly: **"We prove
  unconditionally..."** No RH, no box hypothesis, no zero-density hypothesis anywhere in
  the top-level theorems. Confirmed independently by the Lean repository's own audit
  claim (see below) and by direct inspection of the Lean theorem *types*, which "carry no
  hypotheses" (the paper's own words, Appendix A).

## Exact theorem statements (paper §1.1, verbatim from extracted text)

Counting functions, for `0 ≤ T1 < T2`, `ρ = β + iγ` a nontrivial zero with multiplicity `m_ρ`:

- `N(T1,T2) = Σ_{T1<γ≤T2} m_ρ` — zeros counted with multiplicity
- `N_d(T1,T2) = #{ρ : T1<γ≤T2}` — distinct zeros
- `N*_0(T1,T2) = #{ρ : T1<γ≤T2, β=1/2}` — distinct zeros on the critical line
- `N^s_0(T1,T2) = #{ρ : T1<γ≤T2, β=1/2, m_ρ=1}` — simple zeros on the critical line
- (also `N_0` = on-line zeros with multiplicity, `N^s` = simple zeros; the ordering
  `N^s_0 ≤ N*_0 ≤ N_0 ≤ N` and `N^s_0 ≤ N_d ≤ N` holds identically, no hypothesis needed)

**Theorem A.** As `T → ∞`:
- (i) `N^s_0(T,2T) ≥ (2/3 − o(1)) N(T,2T)`
- (ii) `N_d(T,2T) ≥ (5/6 − o(1)) N(T,2T)`

This is a genuine `liminf`-type asymptotic statement, stated and Lean-formalized in the
correct `∀ε>0, ∃T0, ∀T≥T0, (c−ε)·N(T,2T) ≤ N₀star(T,2T)` form — **not** hardened into
`∀T`. (Verified directly from the reproduced Lean source in Appendix A — see below.) Also
holds for `(0,T)` in place of `(T,2T)`, with rate `O(log log T / log T)`.

**With the Montgomery–Taylor window** `ψ_MT` in place of the indicator window `ψ_0`, the
constants improve to:
- `2 − c_MT⁻¹ = 0.67250...`
- `(1/2)(3 − c_MT⁻¹) = 0.83625...`

where **`c_MT⁻¹ := (1/2)·cot(1/√2) + 1/√2`** — an exact closed-form real number, not a
decimal literal. Optimality among windows `ψ` (of the form `2 − R(ψ)`) is cited to
[CCLM17, Cor. 14]. **This is the theorem the headline "67.25%" figure refers to — it is
Theorem D in the paper (`Zeta23.ThmD.thmD₀` in Lean), a corollary of Theorem A with a
better window, not a separate mechanism.** Per the user's standing instruction, the
formalization target should carry `c_MT⁻¹` symbolically, not `0.6725` as a literal.

**Theorem B.** Theorem A holds verbatim for `L(s,χ)` in place of `ζ(s)`, for any fixed
primitive Dirichlet character `χ`.

**Bonus (§6, ξ′ zeros).** Six further statements for the derivative `ξ′`: flat window gives
85.838% simple-and-on-line (this is Farmer–Gonek–Lee's [FGL14] RH-conditional constant
**with RH removed** — explicitly stated as such); quartic window gives 86.864%, which
exceeds Wu's unconditional 86.957% only for the *simplicity* content, not the raw
on-line count.

## The exact replacement lemma (Step 6 RED-ALERT target)

This is the highest-priority object named in the Thread S brief, and it is stated
explicitly and unambiguously in the paper's own text (§1.3, "Context"):

> "Montgomery's prime-side evaluation is a mean value of a Dirichlet polynomial of length
> T and is unconditional; **RH entered only to read the zero side termwise as a positive
> sum over real ordinates.**"

> "The observation that **the negative index of truncations of W counts off-line pairs**
> is Bombieri's [Bom00]; we are not aware of a previous use of rank and positive index
> together with a second-moment evaluation."

**OLD (RH-dependent) step:** Montgomery 1973 reads the zero-side sum termwise as *purely
positive*, which requires knowing every zero is on the line (RH) — otherwise an off-line
pair contributes an indefinite (not positive) block and the termwise reading fails.

**NEW (unconditional) replacement, precisely:** Truncate/compress Weil's Hermitian form to
a finite window; decompose `G̃ = P + Q` where every distinct on-line zero contributes a
**rank-one positive** block to `P`, and every off-line pair `{ρ, 1−ρ̄}` contributes a
**signature-(1,1)** block to `Q` (Bombieri's observation — the *negative* index of the
truncated form counts off-line pairs, unconditionally, by Sylvester's law of inertia
applied to that finite compression — no assumption about *how many* off-line pairs there
are, or where they sit). Then a purely linear-algebraic **rank–trace inequality**
(paper's Lemma 3.2, reproduced verbatim below) converts an upper bound on `n₊(Q)` (via the
Hilbert–Schmidt/second-moment bound `(P)`) plus the trace identity `(Z)` into a *lower*
bound on `rank P₁` (the simple-on-line part), without ever needing `n₊(Q) = 0`.

**The load-bearing linear-algebra lemma (paper's (1.1), Lemma 3.2):**

> For Hermitian `P1 ⪰ 0` and Hermitian `Q'` with `n₊(Q') ≤ b`:
> `rank P1 ≥ 2·tr P1 + 4·tr Q' − 4b − ‖P1 + Q'‖²_HS`

Stated by the paper itself as "the matrix form of `m² ≥ 2m − 1`" (i.e. for a single
eigenvalue block of multiplicity `m`, `rank` vs `trace²`-type comparison). **This is the
one lemma Thread S Step 1/1A should target as the load-bearing result** — everything else
in the mechanism (the trace identity `(Z)`, the second-moment bound `(P)`) is either
bookkeeping or an external analytic input (Montgomery's unconditional prime-side second
moment, itself citing Aryan [Ary22] and Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh
[BGSTB24]).

## Dependency tags (Step 0 taxonomy)

| Object | Tag | Notes |
|---|---|---|
| Theorem A (2/3, 5/6) | **UNCONDITIONAL** | Confirmed by abstract + Lean types "carry no hypotheses" |
| Theorem D (67.25%, 83.625%) | **UNCONDITIONAL** | Corollary of A with the optimal window; constant is `2 − c_MT⁻¹`, symbolic |
| Theorem B (Dirichlet L-functions) | **UNCONDITIONAL** | Verbatim analogue of A |
| arXiv:2501.14545 (Baluyot et al.) | **ASSUMES-BOX** | Narrow-box `b/log T → 0` hypothesis; one of Theorem A's ancestors, not its statement |
| arXiv:2306.04799 (Baluyot et al., "unconditional Montgomery form factor") | **UNCONDITIONAL** | The prime-side second-moment input `(P)`, cited via [BGSTB24] |
| Aryan [Ary22] Fejér-kernel second moment | **UNCONDITIONAL** | Named analytic input to `(P)` |
| Rank–trace inequality, Lemma 3.2 | **FINITE-DIMENSIONAL** | Pure linear algebra — the Thread S Step 1 target |
| Bombieri 2000 [Bom00] negative-index observation | **FINITE-DIMENSIONAL** | Structural fact about truncations of `W`, no RH |
| Under-RH comparanda (0.6792 [CGdL20], 0.8825/0.9412 [CGdL20]) | **ASSUMES-RH** | Explicitly stated by the paper as stronger but conditional, "a regime the present method does not enter" — cited only for context, not used |

No `UNKNOWN` tags were needed — every dependency's status is stated explicitly in the
source text.

## The Lean artifact (already exists, already verified — read, not reproduced from scratch)

Repository: `https://github.com/anthropics/zeta-23-lean`, tag `v1.0`, Apache 2.0.
Toolchain: **Lean v4.33.0-rc2, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`** —
**newer than GPPVerify's pin** (`v4.19.0` / `c44e0c8`). This is a real practical
constraint: APIs available there are not guaranteed to exist, or to have the same name, at
GPPVerify's pin. Do not port declarations by name without re-verifying against GPPVerify's
own pinned Mathlib source (per the standing loogle/pin-mismatch lesson already recorded in
`docs/FORMALIZATION_PLAN.md`).

Audit claim from the paper's own Appendix A (independently reproduced by GPPVerify's own
discipline, not merely trusted): `#print axioms` on `Zeta23.two_thirds_on_critical_line`,
`Zeta23.thmB0_mult`, `Zeta23.thmC0_mult`, and the Montgomery–Taylor/Theorem-B analogues
returns only `propext, Classical.choice, Quot.sound`, with no `sorry`. Sorries exist only
in `comparator/` challenge/spec files, explicitly documented as intentional (a checker
harness, not a proof gap).

Reproduced Lean theorem statement (paper Appendix A, `Zeta23/Unconditional.lean`):
```
theorem two_thirds_on_critical_line :
  ∀ ε > 0, ∃ T0 : ℝ, ∀ T ≥ T0, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T)
```
Correct `liminf`-shape, exactly as the Thread S brief requires — confirms the source does
**not** need correcting on this point (the paper's own Lean does not silently strengthen
the asymptotic).

Repository layout of direct relevance to Thread S Step 1/2/4:
`Zeta23/LinAlg/` — "Rank–trace inequality, Sylvester inertia, von Neumann trace,"
namespace `RHLinalg`, marked "original development by paper authors" (i.e. not ported
from Mathlib — built from scratch, same situation GPPVerify is in at its own, older pin).

## What Thread S in GPPVerify should and should not do with this

**Should not:** copy `Zeta23/LinAlg/` verbatim. It is pinned to a different, newer Mathlib;
porting without re-verification would violate the standing pin-discipline rule, and a
verbatim copy adds nothing GPPVerify does not already have access to by reading the
Anthropic repo directly.

**Should:** build an independent, GPPVerify-native `SignatureInertia.lean` at GPPVerify's
own pin — informed by having read the mechanism precisely (this document), but derived
against `c44e0c8`'s own `Matrix.IsHermitian` API (see `MATHLIB_RECON.md`). The value is
not re-deriving Anthropic's theorem — it is producing a GPPVerify-native inertia core that
can be honestly bridged (Step 4) to `WeilPositivityCriterion.lean` and
`CauchyKernelPositive.lean`, which is a real question about GPPVerify's own tower that
reading someone else's repo cannot answer for it.
