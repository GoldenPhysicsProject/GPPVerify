# Formalization Plan — the hard targets

*Living document. Updated in every PR that advances it. Ordering is by value-to-risk;
each thread names its exact mathematical route, the Mathlib tools it depends on (verified
against the pinned commit `c44e0c8` / v4.19.0 before writing proofs, per session
discipline), and its honest boundary — what is deliberately NOT claimed.*

*Standing rules: no `sorry` ever committed; no axiom asserting an open claim; "unknown
identifier" = missing import, "unknown constant" = wrong name; every uncertain lemma
name/signature verified via loogle + pinned-commit source before use; one thread = one or
more small PRs, each CI-green before merge.*

---

## Thread D — Finite Weil-positivity criterion ⇒ RH (conditional, fully rigorous)

**Status: DONE — PR #65 (`WeilPositivityCriterion.lean`), CI-green first try.**

The honest formal content of Yakaboylu Thm 5.1 + Prop 5.3 (Bombieri refinement) at the
finitely-supported level, as one real theorem chain:

1. `pairedForm ι S c := Σ_{ρ ∈ S} conj(c(ι ρ)) · c(ρ)` — the Weil/Yakaboylu quadratic
   form on a finite set of zeros. (D1)
2. `involution_fixed_of_pairedForm_nonneg`: if `Z` is closed under an involution `ι` and
   the form is PSD on every finite subset of `Z`, every point of `Z` is a fixed point of
   `ι`. Proof: the −2 test vector (PR #64's kernel upgraded to the actual criterion). (D1)
3. `zetaInvolution ρ := 1 − conj ρ` is an involution; its fixed locus is exactly
   `Re ρ = 1/2`. (D2)
4. The nontrivial zero set `{ρ | ζ(ρ) = 0, 0 < Re ρ < 1}` is closed under
   `zetaInvolution` — genuinely proved, via `GppRH.zeta_zero_implies_companion_zero`
   (functional equation + the repo's own proved conjugation symmetry), with the
   `ρ ≠ −n`, `ρ ≠ 1` side conditions discharged from the strip bounds. (D3)
5. **`rh_iff_weil_pairedForm_nonneg`** (both directions): every nontrivial zero has
   `Re = 1/2` **iff** the paired form is PSD on every finite subset of the zero set.
   (⇐ is the criterion; ⇒ collapses the form to `Σ|c_ρ|²` via `diagonal_form_nonneg`.)

*Boundary: the analytic input that would DISCHARGE the positivity hypothesis (Ŵ ≥ 0 via
operator compression, or Weil's explicit formula) is not claimed — this is the rigorous
reduction, not a proof of RH.*

## Thread C2 — `∫₀^∞ u·sech²(u) du = log 2` (real improper integral, exact value)

**Status: in progress — `SechSquaredIntegral.lean`, lands with the PR updating this line.
All anchors verified at the pinned commit before writing:
`integral_Ioi_of_hasDerivAt_of_nonneg` (IntegralEqImproper:811), `Real.hasDerivAt_sinh`/
`_cosh` (Trigonometric/Deriv:531/551), `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`
(Exp:270), `Real.tendsto_exp_neg_atTop_nhds_zero` (Exp:221), `HasDerivAt.log`,
`Real.cosh_sq_sub_sinh_sq`, `Real.tanh_eq`, `Real.continuousAt_log`.**

Route (no series interchange needed — the antiderivative trick):
- `F(u) := u·tanh u − log(cosh u)` has `F' (u) = u·sech² u` (mechanical `HasDerivAt`
  algebra; if `Real.tanh` lacks derivative lemmas at the pinned commit, work with
  `sinh/cosh` quotients — `Real.cosh_pos` clears denominators).
- `F(u) → log 2` at `atTop`: `log cosh u = u − log 2 + log(1 + e^{−2u})` and
  `u·tanh u − u → 0` (both from `exp` asymptotics).
- Integrand is nonnegative on `Ioi 0`, so
  `MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg` (VERIFY exact name/signature at
  pinned commit before writing; fallback: `..._of_tendsto` + separate integrability via
  comparison) yields both integrability and the value `log 2 − F(0) = log 2`.

*Payoff: this is `η(1) = log 2` in its integral disguise — the normalization constant in
Yakaboylu's biorthogonality (eq. 50) — obtained without touching series.*

## Thread A2 — `N_{1/2} = log 2/6 − 1/24` (rh_cesaro_v2 Prop 5.2, exact value)

**Status: open. After C2 (same machinery).**

Same machinery as C2, longer computation:
- Antiderivative `F₄(u) := (1/3)(u·tanh u·sech²u + sech²u/2 + 2u·tanh u − 2·log cosh u)`
  has `F₄' = u·sech⁴u` (derived by hand; the identity `tanh² = 1 − sech²` does the work).
- `F₄(∞) = (2/3)log 2`, `F₄(0) = 1/6` ⇒ `∫₀^∞ u·sech⁴u du = (2/3)(log 2 − 1/4)`.
- Then `N_{1/2} = (1/4)·∫₀^∞ u·sech⁴u du = log 2/6 − 1/24` after the `t = 2u`
  substitution in the defining integral (`(1/16)∫ t/cosh⁴(t/2) dt`); the substitution
  step needs `integral_comp_mul_left`-style lemmas (VERIFY names).

## Thread A1 — `N_σ` finite and positive for all `σ ∈ (0,1)` (eigenstate norms are real)

**Status: open. After A2.**

- Integrand `t^{2σ}/cosh⁴(t/2)` continuous and positive on `Ioi 0`.
- Integrability by comparison: `cosh(t/2) ≥ e^{t/2}/2` ⇒ integrand `≤ 16·t^{2σ}e^{−2t}`;
  reduce to the Gamma integrand via scaling (`Real.GammaIntegralConvergent` +
  `integrableOn` under `x ↦ 2x`; VERIFY the comp-mul-left integrability lemma) or prove
  the `e^{−2t}` version directly.
- Positivity of the integral: `setIntegral_pos_iff_support`-style lemma (VERIFY) or
  bound below on `[1,2]`.

*Payoff: "the eigenstates are genuine L² elements" — the fact Theorem 3.5's
square-integrability claim rests on, for every point of the critical strip.*

## Thread C1 — alternating harmonic series `Σ(−1)^{k}/(k+1) = log 2`

**Status: open (only if genuinely absent from Mathlib — re-search first:
`Real.tendsto_sum_range_div…`, `hasSum` forms, Abel-summation theorems).**

Fallback proof if absent, fully elementary: partial-sum identity
`Σ_{k<n}(−1)^k x^k = (1 − (−x)^n)/(1+x)` integrated over `[0,1]`:
`log 2 = Σ_{k<n} (−1)^k/(k+1) + R_n` with `|R_n| ≤ ∫₀¹ x^n = 1/(n+1) → 0`.
All finite sums + `intervalIntegral` + squeeze — no boundary Abel theorem needed.

## Thread B — HaarPositivityWeil convolution-square integrability gap

**Status: open, last (hardest bookkeeping).**

`convolution_square_positive_type` was honestly stubbed (PR #45) pending Lp/L² membership
of pairwise-translated products. Route: restrict to continuous compactly-supported `f`
(`C_c`), where `MeasureTheory.Continuous.integrable_of_hasCompactSupport` and the
convolution API (`MeasureTheory.convolution`) give the bookkeeping for free; prove
positive-typeness `Σ_{i,j} conj(a_i) a_j (f⋆f̃)(x_i⁻¹x_j) ≥ 0` there. VERIFY the pinned
commit's convolution API surface first — if too thin, narrow to the discrete/compact case
where sums replace integrals.

---

*History: earlier arcs (p-adic Tate thread PRs #44–58, Cesàro/Abel/Yakaboylu elementary
layer PRs #59–64) predate this document; see git log. Thread completions are recorded
here as they merge.*
