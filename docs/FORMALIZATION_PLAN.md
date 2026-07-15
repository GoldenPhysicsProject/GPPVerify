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

**Status: DONE — PR #66 (`SechSquaredIntegral.lean`). Two CI lessons recorded: the
exp-form `Real.tanh_eq` does not exist at the pinned commit (route through
`tanh_eq_sinh_div_cosh` + `sinh_eq`/`cosh_eq`), and bare `simpa` can rewrite a tendsto
GOAL into a different statement via the default simp set — use have-ascribed terms
(defeq eats `Function.comp`/beta) plus `simpa only [...]`.**

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

**Status: DONE — PR #67 (`SechFourthIntegral.lean`). The tanh-polynomial design worked as
planned. Three more pinned-commit lessons recorded: `Real.sinh_nonneg`/`Real.tanh_lt_one`
are master-only (first-principles replacements from `sinh_eq`/`cosh_eq` + exp
monotonicity), `ring` treats `id x` as an atom distinct from `x` (`simp only [id_eq]`
first), and `HasDerivAt.comp` needs the composition-form ascription plus the explicit
point to elaborate (`(hg).comp t hf` against a goal stated with `∘`).**

Same machinery as C2, longer computation:
- Antiderivative `F₄(u) := (1/3)(u·tanh u·sech²u + sech²u/2 + 2u·tanh u − 2·log cosh u)`
  has `F₄' = u·sech⁴u` (derived by hand; the identity `tanh² = 1 − sech²` does the work).
- `F₄(∞) = (2/3)log 2`, `F₄(0) = 1/6` ⇒ `∫₀^∞ u·sech⁴u du = (2/3)(log 2 − 1/4)`.
- Then `N_{1/2} = (1/4)·∫₀^∞ u·sech⁴u du = log 2/6 − 1/24` after the `t = 2u`
  substitution in the defining integral (`(1/16)∫ t/cosh⁴(t/2) dt`); the substitution
  step needs `integral_comp_mul_left`-style lemmas (VERIFY names).

## Thread A1 — `N_σ` finite and positive for all `σ ∈ (0,1)` (eigenstate norms are real)

**Status: DONE — PR #68 (`EigenstateNormStrip.lean`), CI-green first try. Includes the
`eigenstateNorm_at_half` consistency corollary tying A1 to A2's exact value.**

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

**Status: in progress — `AlternatingHarmonicLog2.lean`, lands with the same PR as
Thread B (this line's PR). Absence at the pinned commit confirmed by direct source
inspection:
`hasSum_pow_div_log_of_abs_lt_one` stops strictly inside `|x| < 1`, the alternating series
*test* (SpecificLimits/Normed:712) gives convergence but no value, and no Abel-summation
boundary theorem exists. Anchors verified: `geom_sum_eq` (GeomSum:282), `integral_pow`
(Integrals:401), `integral_one_div` (Integrals:454), `integral_finset_sum`
(IntervalIntegral/Basic:627), `integral_const_mul` (:655), `integral_comp_add_right`
(:761).**

Fallback proof if absent, fully elementary: partial-sum identity
`Σ_{k<n}(−1)^k x^k = (1 − (−x)^n)/(1+x)` integrated over `[0,1]`:
`log 2 = Σ_{k<n} (−1)^k/(k+1) + R_n` with `|R_n| ≤ ∫₀¹ x^n = 1/(n+1) → 0`.
All finite sums + `intervalIntegral` + squeeze — no boundary Abel theorem needed.

## Thread B — HaarPositivityWeil convolution-square integrability gap

**Status: in progress — `ConvolutionSquarePositive.lean`, lands with the same PR as C1
(this line's PR). Scope chosen: integrable *bounded* `f` on `ℝ` with Lebesgue (= Haar)
measure — exactly the hypothesis set PR #45's stub proposed, stronger than the `C_c`
fallback originally sketched here. Anchors verified at pinned commit:
`Integrable.bdd_mul` (L1Space/Integrable:436), `integral_finset_sum` (Bochner/Basic:241),
`integral_mul_right_eq_self` + `Integrable.comp_mul_right` with `@[to_additive]`
(Group/Integral:97/132). The idèle-class-group version stays open for the honest reason
recorded in the source file: idèle class groups are not in Mathlib.**

---

---

# Phase 2 — multi-domain mining (whole document library, not only RH)

*Scouted 2026-07-15 from the full uploads library. Same rules: verify anchors at the
pinned commit first, honest boundaries, one thread = small CI-green PRs.*

## Thread P — the Planck integral `∫₀^∞ x³/(eˣ−1) dx = π⁴/15`

From `blackbody_law_qg_v1.tex` (the Stefan–Boltzmann quartic). Route: geometric expansion
`1/(eˣ−1) = Σ_{n≥1} e^{−nx}` on `(0,∞)`, term integrals `∫ x³e^{−nx} = 6/n⁴`
(Gamma-integral scaling), sum `6·ζ(4) = 6·π⁴/90 = π⁴/15`. Needs: `integral_tsum`
(summability of the norms is `Σ 6/n⁴ < ∞`), Mathlib's `riemannZeta_four` (VERIFY at
pinned; else route through `hasSum_zeta_four`-style Basel machinery). Same grade as
threads C2/A2 — genuinely hard, fully real.

## Thread M — Mellin kinematics elementary layer

From `mellin_kinematics.tex`: (M1) *power laws are the continuous homomorphisms of
`(ℝ⁺,×)`* — classification via log/exp conjugation to additive Cauchy + continuity
(check what Mathlib has for continuous additive ℝ-homs being linear); (M2) *Mellin
reflection* — the `x ↦ 1/x` change of variables on `((0,∞), dx/x)`, connecting to the
existing inversion-invariance layer; (M3) *uniqueness of the quadratic scale transport*
(the origin of `Δ = 2s`) — likely elementary uniqueness, verify statement first.

## Thread Z — zitterbewegung arithmetic layer

From `zitterbewegung_T_boundary_FINAL.tex`: the frequency proposition
(`ω = 2mc²/ℏ` from shadow symmetry — exact arithmetic) and any boundary-oscillation
content not already covered by `CoreTheorems.lean`'s oscillator lemmas and
`MajoranaCondition.lean`. Read the theorem statements in full before scoping.

*Standing honesty note: nobody is proving RH itself here, and this plan does not pretend
otherwise. The value is that every reduction and every constant in the surrounding tower
is kernel-checked, with each remaining gap precisely named.*

---

*History: earlier arcs (p-adic Tate thread PRs #44–58, Cesàro/Abel/Yakaboylu elementary
layer PRs #59–64) predate this document; see git log. Thread completions are recorded
here as they merge.*
