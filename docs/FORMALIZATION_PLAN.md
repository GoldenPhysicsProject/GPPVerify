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

**Status: DONE — PR #70, `QuantumGravity/PlanckIntegral.lean`, one CI round (lessons:
`norm_num at h` can reduce a hypothesis like `Γ(4)=6`-in-progress to `True` — rewrite the
goal instead; `positivity` won't prove `1 ≤ (n:ℝ)+1`, use `nlinarith [Nat.cast_nonneg n]`;
`field_simp` closed `planck_summand_eq` outright, trailing `ring` errored "no goals").
All anchors verified at the pinned commit:
`integral_rpow_mul_exp_neg_mul_rpow` (Integral/Gamma:39, exact form
`b^(−(q+1)/p)·(1/p)·Γ((q+1)/p)`), `integral_tsum_of_summable_integral_norm`
(DominatedConvergence:152, `∑'∫ = ∫∑'`), `hasSum_zeta_four` (ZetaValues:335),
`Real.Gamma_nat_eq_factorial` (Gamma/Basic:323), `Real.exp_lt_one_iff`/`one_lt_exp_iff`
(Data/Complex/Exponential:328/323), `hasSum_nat_add_iff` (InfiniteSum/NatInt),
`Complex.exp_nat_mul` (:145 — Real twin assumed, fallback: derive by induction).**

From `blackbody_law_qg_v1.tex` (the Stefan–Boltzmann quartic). Route: geometric expansion
`1/(eˣ−1) = Σ_{n≥1} e^{−nx}` on `(0,∞)`, term integrals `∫ x³e^{−nx} = 6/n⁴`
(Gamma-integral scaling), sum `6·ζ(4) = 6·π⁴/90 = π⁴/15`. Needs: `integral_tsum`
(summability of the norms is `Σ 6/n⁴ < ∞`), Mathlib's `riemannZeta_four` (VERIFY at
pinned; else route through `hasSum_zeta_four`-style Basel machinery). Same grade as
threads C2/A2 — genuinely hard, fully real.

## Thread M — Mellin kinematics elementary layer

**Status: DONE — PR #71, `CelestialHolography/MellinKinematics.lean`, one CI round
(lesson: `nlinarith` failed on `h : φ (1 * 1) = φ 1 * φ 1` because `φ (1 * 1)` and `φ 1`
are distinct atoms — `rw [one_mul] at h` first). Anchors verified at pinned: `AddMonoidHom.toRealLinearMap` +
`coe_toRealLinearMap` (Topology/Instances/RealVectorSpace),
`MeasureTheory.integral_comp_rpow_Ioi` (IntegralEqImproper, exact form
`∫ (|p|·x^{p−1}) • g(x^p) = ∫ g`). Honesty correction recorded: the paper's
classification lemma asserts a unique `α > 0`, but constants and inversion are continuous
homs too — formalized with the correct `α : ℝ`.**

From `mellin_kinematics.tex`: (M1) *power laws are the continuous homomorphisms of
`(ℝ⁺,×)`* — classification via log/exp conjugation to additive Cauchy + continuity
(check what Mathlib has for continuous additive ℝ-homs being linear); (M2) *Mellin
reflection* — the `x ↦ 1/x` change of variables on `((0,∞), dx/x)`, connecting to the
existing inversion-invariance layer; (M3) *uniqueness of the quadratic scale transport*
(the origin of `Δ = 2s`) — likely elementary uniqueness, verify statement first.

## Thread Z — zitterbewegung arithmetic layer

**Status: DONE — PR #72, `QuantumGravity/ZitterbewegungShadow.lean`, one CI round
(lesson confirmed twice: `field_simp` leaves an `E*E` vs `E^2` npow residue — close with
`ring`). Contents: `shadow_energy_eq` (μ·e^{−log(E/μ)} = μ²/E exactly, the
one analytic step — `exp_neg` + `exp_log` + `field_simp`), `shadow_splitting` /
`shadow_splitting_onshell`, `shadow_frequency_onshell` ((E+E²/E)/ℏ = 2E/ℏ, the
Zitterbewegung frequency 2mc²/ℏ at E = mc²), `beat_frequency` (|E/ℏ−(−E/ℏ)| = 2E/ℏ),
`mirror_dm_bound` (Ω_mirror = Ω_b ≤ Ω_DM ⇒ Ω_DM/Ω_b ≥ 1 via `le_div_iff₀`). Physics
identifications carried as hypotheses/documentation, never smuggled.**

From `zitterbewegung_T_boundary_FINAL.tex`: the frequency proposition
(`ω = 2mc²/ℏ` from shadow symmetry — exact arithmetic) and any boundary-oscillation
content not already covered by `CoreTheorems.lean`'s oscillator lemmas and
`MajoranaCondition.lean`. Read the theorem statements in full before scoping.

## Thread K — the Cauchy kernel is positive-type (form-domain note companion)

**Status: DONE — PR #74, `RiemannHypothesis/CauchyKernelPositive.lean`, two CI rounds.
Lessons: (1) ascribing a lambda application directly to `ℂ` makes the elaborator build
the body's division in `ℂ` (`HDiv ℝ ℝ ℂ` failure) — inner-ascribe `(… : ℝ)` first so the
ofReal coercion is inserted outside; (2) `ContinuousAt.tendsto` produces the
beta-REDUCED value `f 0`, so a `rw` equation for it must be stated reduced, not as
`(fun x => …) 0`; (3) `rw [integral_const_mul]` is ambiguous when the integrand has a
nested constant layer `∫ w·(ε·g)` — both sides match; use `simp only
[integral_const_mul]` to normalize to fixpoint. All the analysis (damped-cosine
antiderivative, sandwich, Gram squares, complex note objects) compiled first-try.** Companion to the form-domain note on Yakaboylu Thm 5.1
(`yakaboylu_form_domain_note.pdf`): the note splits the finite-ε structure of eq. (75)
into a provable on-line half and a provably failing off-line half, and this thread
kernel-checks both. (K1) `integral_exp_neg_mul_cos`: `∫₀^∞ e^{−bt}cos(xt)dt = b/(b²+x²)`
by explicit antiderivative `e^{−bt}(x·sin−b·cos)/(b²+x²)` + sandwich decay, via
`integral_Ioi_of_hasDerivAt_of_tendsto'` (verified at pinned, IntegralEqImproper:750 —
the signed-integrand twin of the `_of_nonneg` version used by Threads C2/A2). (K2)
`cauchy_kernel_positive_type`: `PositiveType (ε²/(ε²+x²))` reusing Thread B's skeleton
(`Complex.re_sum` → `mul_ofReal_re` → `integral_finset_sum` → pointwise
`gram_square_nonneg` twice, on cos and sin amplitudes, after `Real.cos_sub`). (K3) the
note's Prop 2.1 (`matrix_element_off_line_diag`, `off_line_diag_neg`: diagonal
`ε²/(ε²−4δ²) < 0` for `ε < 2δ`), the on-line reduction `matrix_element_on_line`
(element = Cauchy kernel, exact complex algebra), and eq. (7)
(`tendsto_offline_min_eigenvalue`: `d(ε)−1 → −1`). Numerics cross-checked on the
100k-zero dataset (two independent runs, δ = 0.05/0.01, identical structure: resonance
at ε = 2δ exactly, λ_min → −1, test vector → −2 matching PR #65's lemma). Anchors
verified: `exp_neg_integrableOn_Ioi` (ExpDecay:28), `HasDerivAt.cos/.sin` (Trig/Deriv:
671/695), `HasDerivAt.exp` (ExpDeriv:284), `Complex.conj_I` (Complex/Basic:461),
`setIntegral_nonneg` (Bochner/Set:686), `Finset.sum_add_distrib` (to_additive of
`prod_mul_distrib`, Finset/Basic:267). NOT claimed: ε→0 uniformity over infinite zero
sets — equivalent to RH by `rh_iff_weil_pairedForm_nonneg`, stays open.

## Thread S — the zeta bridge `∫₀^∞ t^{s−1}/sinh t = 2(1−2^{−s})Γ(s)ζ(s)`

**Status: DONE — PR #75, `QuantumGravity/SinhZetaBridge.lean`, six CI rounds. The lesson
chain, in order of discovery: (1) inline `(by positivity)`/`(by linarith)` term-mode args
elaborate against metavariable-typed goals and stick on `IsOrderedRing ?m` — hoist into
typed `have`s; (2) an UN-ASCRIBED cast in a hint list (`nlinarith [Nat.cast_nonneg k]`)
leaves the target type meta — ascribe (`(Nat.cast_nonneg k : (0:ℝ) ≤ k)`) or hoist;
(3) `set_option ... in` must precede the DOC COMMENT, not sit between it and `theorem`;
(4) THE BIG ONE: an implicit function argument whose occurrences are applications
(`?f (2*k)` in `tsum_even_add_odd`) is a non-Miller higher-order unification problem —
the unifier can dive into unbounded `whnf` unfolding of `tsum`'s classical-choice
definition (survived 1.6M heartbeats). Pass such implicits EXPLICITLY
(`tsum_even_add_odd (f := ...)`). Also: state such `he`/`ho` hypotheses in literal redex
form `(fun n => ...) (2*k)` so first-order matching works; route subseries summability
through `Summable.comp_injective` (Group:304 to_additive) rather than
`of_nonneg_of_le` comparisons.** From `kinematic_block_v11.tex` (Prop. zetabridge, "verified to 29 digits")
and `haar_qg_paper_v2151.tex` (first Plancherel moment `M₁ = 1/8`). Thread P's proof one
level up: residue expansion `1/sinh t = 2Σe^{−(2k+1)t}`, real-exponent Gamma term
integrals (`integral_rpow_mul_exp_neg_mul_rpow` at `q = s−1`, no npow bridge), odd
Dirichlet split `Σ(2k+1)^{−s} = (1−2^{−s})Σn^{−s}` via `tsum_even_add_odd` (to_additive
of `tprod_even_mul_odd`, NatInt:205 — state `he`/`ho` in REDEX form `(fun n => …) (2*k)`
so the implicit `f` unifies first-order), interchange via
`integral_tsum_of_summable_integral_norm`. Corollaries: `∫ t/sinh t = π²/4`
(`M₁ = 1/8` π-free), `∫ t³/sinh t = π⁴/8`. Other anchors verified at pinned:
`summable_one_div_nat_rpow` (PSeries:297), `summable_nat_add_iff` (to_additive,
NatInt:227), `one_div_le_one_div_of_le` (Order/Field/Basic:110), `hasSum_zeta_two`
(ZetaValues:330).

## Thread E — the Euler-sum capstone (`M₂ = 1/90 = ζ(4)/π⁴`)

From `haar_qg_paper_v2151.tex` base case `L = 2`: the two linear Euler sums
`Σₙ (ζ(2)−H_n⁽²⁾)/n² = π⁴/120 = (3/4)ζ(4)` and
`Σₘ (ζ(3)−H_{m−1}⁽³⁾)/m = π⁴/72 = (5/4)ζ(4)`, whose sum `2ζ(4) = π⁴/45` gives
`M₂ = 1/90`. The first reduces to the symmetric double-sum decomposition
`2·Σ_{m≤n} 1/(m²n²) = ζ(2)² + ζ(4)` — pure ℕ×ℕ tsum bookkeeping plus Mathlib's
`hasSum_zeta_two/four`. The second is Euler's `Σ Hₙ/n³ = (5/4)ζ(4)` — genuinely harder
(partial-fraction reindexing over ℕ×ℕ); attempt in full, and if it resists, land the
first sum + the assembly with the second's exact gap named. The reduction of the 2-D
Plancherel integral to `Σ min(m,n)/(m²n³)` (real Fubini on ℝ²) is a separate follow-up,
not claimed by this thread.

## Thread L — the Weil support ladder (Connes–Consani rung structure)

**Status: DONE — PR #76, `RiemannHypothesis/WeilSupportLadder.lean`, one CI round
(lessons: `integral_comp_abs` lives in `Mathlib.MeasureTheory.Measure.Lebesgue.Integral`
— unknown IDENTIFIER = missing import, per the standing rule; and the pattern-capture
trap again — `rw [mul_neg]` grabbed `-ε * -u` inside the exp argument by traversal order
instead of the intended `x * -u`; use a targeted `rw [show x * -u = -(x*u) by ring]`).
The numerical twin (Thread N) used exactly this file's truncation identity for its prime
side and matched the 100k-zero sum to 16 digits.** From arXiv:2106.01715 §2.2 via the joint-session prompt. Contents:
`HasSupportIn`; `convolution_hasSupportIn` (support doubling for convolution squares, by
triangle inequality + pointwise-zero integrand); `primeSide` via Mathlib's
`ArithmeticFunction.vonMangoldt`; `primeSide_term_eq_zero` + `primeSide_eq_truncation`
(exact truncation at `L < log(N+1)`, `tsum_eq_sum`); rung 0
`primeSide_eq_zero_of_support_lt_log_two` (`vonMangoldt_ne_zero_iff` + `IsPrimePow.two_le`
+ `log_le_log_iff`); conditional `weil_nonneg_of_arch_nonneg_rung_zero` (rung-0
archimedean positivity = Connes–Consani analytic input, carried as a NAMED hypothesis);
the ε-dictionary `integral_exp_neg_abs_mul_cos` (`∫ e^{−ε|u|}cos(xu) du = 2ε/(ε²+x²)`,
via `integral_comp_abs` + Thread K's damped-cosine integral). NOT claimed: the
ε-uniformity ⟺ all-rungs equivalence (explicit-formula-deep; = RH via Thread D).
Anchors verified at pinned: `vonMangoldt_apply/_ne_zero_iff` (VonMangoldt:69/88),
`IsPrimePow.two_le` (IsPrimePow:91), `Real.log_natCast_nonneg` (Log/Basic:207),
`Real.log_le_log_iff` (Log/Basic:138), `integral_comp_abs` (green in
ArchimedeanZetaIntegral).

## Thread N — near-null direction of the Weil Gram form at L = 2.2 (numerics)

**Status: DONE — both gates passed; results in the note addendum. GATE 1: the
explicit-formula side and the 100k-zero side of the 10×10 Weil Gram matrix agree to
max|Z−W| = 5.2e-20 (relative 2.2e-16) — sixteen digits, simultaneously certifying the
code and the explicit formula on this class. All ten eigenvalues positive across 13
decades; λ_min = 2.156e-13, ~7 digits above the certified noise floor (a real,
strictly positive near-null direction — no fake negatives). GATE 2: |ĝ_c| suppressed at
γ₁,γ₂,γ₃ by 3e-5/0.013/0.069, minima lock to ordinates, gap-cv 0.14 (no lattice comb).
PREDICTION P4 REFUTED and retracted: Möbius/BD correlation r = 0.10, 95% CI
[−0.19, 0.33] — consistent with zero; at L = 2.2 the near-null direction is archimedean/
low-rung shaped, not yet Möbius-shaped. The BD profile is asymptotic; it does not
describe the small-support extremal.** Protocol per the joint-session prompt: basis `(1−(y/a)²)³·P_n(y/a)` (C² edges → `|ĝ|² ~ t⁻⁸`, zero-side
tail bound ~1e-31 at 100k zeros — the previous session's double-precision Gaussian-bump
landmine is structurally excluded); overlap cond 2.4e5 < 1e6 ✓; GATE 1 = explicit-formula
side (poles G(∓1/2) separable + exact prime truncation at rungs log2..log9 + digamma
archimedean density `(Re ψ(1/4+it/2) − log π)/2π`) vs zero side (100k zeros, γ₁ restored
via mp.zetazero — note the uploaded file STARTS AT ZERO #2); GATE 2 = suppression at
genuine ordinates + minima-gap cv (comb exclusion); then Möbius/BD correlation with block
bootstrap. Results land in the note addendum only if both gates pass; a gate failure is
reported as-is and is itself a result.

## Thread Y — form-domain note v2 addendum

**Status: drafted — `scratchpad/form_domain_note_addendum.tex`** (source .tex of the note
not in this session's uploads; addendum is written for merge, with `\verifiedfigure{}`
slots to be filled exclusively from a gates-passing Thread N run). Contents: quantitative
circularity remark (uniform ε-positivity ⟺ no off-line zeros at any δ ⟺ RH); Bochner
sharpening of §4.1 with the Lean citations (CauchyKernelPositive.lean); new support-ladder
section with rung table and WeilSupportLadder.lean citations.

## Thread Q — the off-line quartet + transport seed (memo fragments, checked)

**Status: DONE — PR #77, `RiemannHypothesis/QuartetPerturbation.lean`, one CI round
(lessons: the DEFAULT simp set can over-rewrite `.re`/`.im` goals through `ofReal`
coercions into `mul_eq_mul_left_iff` disjunctions — use `simp only` with the explicit
`mul_re/mul_im/ofReal_re/ofReal_im/I_re/I_im` list + `ring`; and a `calc` block's first
LHS must match the goal EXACTLY — rewrite conjugate terms via the prepared equation
first).** From the entanglement/shadow-positivity memo (Sonnet session
handoff): (Q1) `quartet_contribution` — the memo §4.3 closed form
`4e^{−C(γ²−δ²)}cos(2Cγδ)` for the functional-equation quartet of an off-line zero under
Gaussian pairing, as an identity in ℂ (Im = 0 included), via `Complex.exp_conj`
(Exponential:165), `Complex.add_conj` (:571), `Complex.exp_re` (Data/Complex/
Trigonometric:506), `Complex.I_sq`; plus `pair_contribution` (on-line `2e^{−Cγ²}`).
(Q2) sign mechanism: negative iff `cos(2Cγδ) < 0` (both directions, nlinarith with
product hints) + envelope amplification `e^{Cδ²} ≥ 1` (`Real.add_one_le_exp`). (Q3)
`positiveType_comp_addMonoidHom`: positivity transports along ANY `ℝ →+ ℝ` (map_sub +
the PositiveType instance at mapped points) — the ℝ-factor seed of the memo's §6.1
idèle transport question; the idèle-level statement stays open (not in Mathlib, the
PR #45 recorded gap). (Q4) `cesaro_gram_sq_nonneg`: the Cesàro datum is shadow-positive
in finite-Gram form (one-line wrapper over PR #61's `abel_state_sq_nonneg`). NOT
claimed: anything about `arithmetic_admissibility` — per the memo's own protocol.
Numerics companion: the memo's §4.2 "monogamy" REPLICATED on a third basis family
(Legendre-weight, the gates-certified Thread N pipeline, N=10, L=2.2, dps 45):
A (poles+arch) min eig −1.391 (indefinite), P (primes) min eig −1.485 (indefinite),
W = A−P min eig +2.156e-13 (PSD, = zero side to 16 digits). The pattern — neither
marginal positive alone, only the difference — now holds across seven basis families of
two distinct types (six Gaussian variants + compact-support Legendre-weight).

## Thread H — the pseudo-isothermal halo pair (Abel projection + inversion, exact)

**Status: in progress — `Cosmology/AbelHaloPair.lean`, lands with the PR updating this
line.** From ONON5213's Dark Matter chapter (`thm:surface-density-haar`,
`thm:abel-inversion`, the boxed profile): (H1) `abel_forward` — the line-of-sight
projection `2∫_b^∞ (r_c²/(r²+r_c²))·r/√(r²−b²) dr = π r_c²/√(b²+r_c²)`, antiderivative
`(2r_c²/A)·arctan(√(r²−b²)/A)`, `A = √(b²+r_c²)` (the `A²+u²` Cauchy-kernel soul);
(H2) `abel_inverse_eval` + `dm_profile_boxed` — the inversion integral
`∫_r^∞ b/(√(b²−r²)·√(b²+r_c²)³) db = 1/(r²+r_c²)`, antiderivative
`(√(b²−r²)/√(b²+r_c²))/(r²+r_c²)`, recovering `ρ₀/(1+(r/r_c)²)` exactly. Machinery:
`integral_Ioi_of_hasDerivAt_of_nonneg` (as C2/A2/K). Anchors verified at pinned:
`Real.hasDerivAt_sqrt` (Sqrt:63), `Real.hasDerivAt_arctan` (ArctanDeriv:75),
`Real.tendsto_arctan_atTop` (Arctan:161), `Real.continuous_arctan` (Arctan:282),
`Real.arctan_zero` (:143). Drift-proof routes chosen: `sqrt_le_sqrt`+`sqrt_sq` instead
of `le_sqrt`; ratio-limit via squaring + `sqrt_sq` instead of `sqrt_div`; explicit
`mul_le_mul_of_nonneg_right` instead of bare `gcongr`. NOT claimed: general Abel
uniqueness (Hankel duality); the chapter's Haar normalization and `ρ₀ = α·ρ_b`
(its Conjecture) physics inputs.

*Standing honesty note: nobody is proving RH itself here, and this plan does not pretend
otherwise. The value is that every reduction and every constant in the surrounding tower
is kernel-checked, with each remaining gap precisely named.*

---

# Phase 3 — arcs merged since this document last tracked (PRs #79–#102)

*This document drifted 22 PRs out of date (last substantive edit: PR #80, 2026-07-17).
Recorded here retrospectively from git log so the drift does not recur. **Update this file
in the same PR that advances a thread** — that is the rule that failed.*

**Weil/criterion layer.** Thread D2 (#79) `TwoPointCriterion.lean` — RH iff pair positivity
on reflection pairs `{ρ, 1−conj ρ}`; the zero side of the Weil criterion carries no analytic
content. Thread S2 (#81) `SchurWeilClass.lean` — positive-type × convolution square is
positive-type, via translated Gram vectors, no spectral theorem. Thread T (#82)
`TruncatedTransport.lean` — rung-level positivity on the S-truncated chart `ℝ × ℤ^S`, one
pullback, no adeles. **#78 retired the `arithmetic_admissibility` axiom** and its
`riemann_hypothesis` alias (they restated RH verbatim); the flagship RH statement is now the
Thread D conditional.

**Thread E — DONE (#83).** The Euler-sum capstone `M₂ = ζ(4)/π⁴ = 1/90`, including Euler's
`Σ Hₙ/n³ = (5/4)ζ(4)`, which the plan had flagged as the step that might resist.

**Li's criterion arc (#94, #97).** `Li's criterion: entire Ξ and the λ₁ closed form`, then
**unconditional `λ₁ > 0`** from `γ > log(4π) − 2`. A genuinely unconditional positivity
result on the Li sequence — the strongest unconditional zeta-side statement in the tree.

**Idèle-group arc (85cd8ae, c7cad4c, #95, #96).** First steps toward the object PR #45
recorded as missing from Mathlib: diagonal embedding injectivity, topological group
structure, a `Subring` bridge lemma for the compactness criterion, and a `RankOne` instance
for the adic valuation. This is the long pole for every "idèle class group" gap named
elsewhere in this plan.

**Mellin/zeta kernel arc (#98, #99).** Mellin transform of the Planck/Bose–Einstein kernel
is `Γ(s)ζ(s)`; the odd-frequency variant matches the black-body paper's exact kernel.
Generalizes Threads P and S from fixed exponents to the transform itself.

**Haar projection arc (#100, #101).** Finite-group instance of the Haar projection theorem
(Reynolds operator), then its range and self-adjointness — a complete, concrete instance of
the projection that the adelic layer can only state.

**Grassmannian / QI layer (#88, #89, #90, #102).** SWAP is not PSD (closing the loop to
Mathlib's `PosSemidef`); general Choi-matrix / complete-positivity infrastructure;
Proposition 2.2 complete (transpose on `M₂(ℂ)` is not completely positive);
`Gr(k,n)` orthogonal-complement self-duality (Ch. 7), generalizing the paper's own
`Gr(2,4)` case.

**Spectral/spinor layer (#84–#87).** Theorem 4.1(b)–(d) clock-locking special values and the
γ₅ identity; `momentum_spinor_decomposition` (Lemma 2.1(c)); `zeta_zero_forces_companion_zero`
promoted from a stale stub to a real proof; and the momentum generator has no L² point
spectrum (pinning down the `thm:no-ghosts-onon` gap).

---

# Phase 4 — the axiom ledger, and the next boundary

## Retired this session: `schwartz_integral_clm_exists`

**Status: DONE — now a theorem, kernel-verified.** Mathlib v4.19.0 already had the tool:
`SchwartzMap.integralCLM` (Analysis/Distribution/SchwartzSpace.lean:1110), integration as a
continuous linear map `𝓢(D,V) →L[𝕜] V` for any `HasTemperateGrowth` measure. On `ℝ`,
`volume` is an additive Haar measure, so
`MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth` (ibid.:600) supplies the
instance, and `integralCLM_apply` is a `rfl` lemma — so the witness is
`⟨SchwartzMap.integralCLM ℝ volume, fun _ => rfl⟩`. Kernel audit after the change:

```
'GppRH.schwartz_integral_clm_exists' depends on axioms:
  [propext, Classical.choice, Quot.sound]          -- i.e. none of ours
'GppRH.temperedness_iff_critical_line' depends on axioms:
  [propext, Classical.choice, GppRH.exp_growth_not_tempered, Quot.sound]
```

`temperedness_iff_critical_line` is down from two custom axioms to one. This is exactly the
"close them one step at a time as Mathlib matures" discipline: the gap was real when written
and is not real any more.

## Next boundary: `exp_growth_not_tempered` — and a subtlety that must be faced first

The one remaining custom axiom on the temperedness scaffold:

```lean
axiom exp_growth_not_tempered (a : ℝ) (ha : a ≠ 0) :
    ¬∃ T : SchwartzMap ℝ ℂ →L[ℝ] ℂ,
      ∀ φ : SchwartzMap ℝ ℂ, T φ = ∫ u : ℝ, cexp (↑a * ↑u) * ↑(φ u)
```

**Do not attempt this as a routine port — the Lean statement is subtler than the
mathematics.** Mathlib's Bochner integral is a *junk value* (`0`) on non-integrable
integrands. Schwartz functions decay faster than every polynomial but *not* faster than
every exponential (e.g. `u ↦ exp(−√(1+u²))` is Schwartz), so `u ↦ e^{au}φ(u)` is genuinely
non-integrable for suitable `φ`, and on exactly those `φ` the defining equation asserts
`T φ = 0` rather than asserting anything divergent. So the informal argument "the integral
diverges, hence no such `T`" does **not** transfer: the contradiction has to come from
*linearity*, not from divergence.

Route to prove it honestly: exhibit Schwartz `φ₁, φ₂` with `e^{au}φᵢ` non-integrable
(so `T φᵢ = 0` by the junk-value convention) but `e^{au}(φ₁+φ₂)` integrable with nonzero
integral — contradicting additivity of `T`. Verify at the pinned commit before writing:
the Schwartz-membership of a chosen `exp(−√(1+u²))`-type witness, and
`MeasureTheory.integral_undef`. If a clean pair resists construction, the honest fallback is
to *restate* the axiom in the form the mathematics actually supports (no continuous extension
of the pairing to all of `𝓢`) rather than leave a statement whose Lean meaning is
accidental. **Restating is allowed; weakening a statement to make it provable while keeping
the strong name is not.**

## Thread HT — the prime–Archimedean heat trace (elementary layer)

**Status: DONE (elementary layer) — `RiemannHypothesis/HeatTraceCriterion.lean`, typechecks
clean first try after two pinned-name fixes; all five results kernel-audited to Lean
built-ins only.**

Source: `arithmetic_principal_series_RH_program34.tex` (the BPY prime–Archimedean spectral
program). The paper reformulates RH as a **zero-independent** statement: with
`𝒦(t) = (4πt)^{-1/2}⟨𝒲, e^{−(·)²/(4t)}⟩` for `𝒲 = ν_∞ − ν_p`,

> **RH ⟺ `𝒦` is completely monotone on `(0,∞)`**, and under RH `𝒦(t) = Σ_{γ>0} m_γ e^{−γ²t}`.

Note the paper states plainly at §intro: *"RH is not claimed."* It also runs its own
circularity audit — one route is rejected in-text as "only RH in different words" — and
carries a long series of explicit no-go theorems (Born kernel not pointwise positive, theta
lift sign-indefinite, no positive exponential tilt, HCM insufficient, Hilbert doubling
insufficient). That is the right posture and it is why this thread was worth mining.

Formalized:
- `CompletelyMonotone` — the definition. **Absent from Mathlib at the pin**; verified by
  direct search, there is no Bernstein/Hausdorff–Widder theory upstream.
- `completelyMonotone_exp_neg` — `t ↦ e^{−at}` is completely monotone for `a ≥ 0`, i.e. the
  single heat mode of `Σ m_γ e^{−γ²t}` at `a = γ²`. Via root-namespace
  `iteratedDeriv_exp_const_mul` and `(-1)ⁿ(-a)ⁿ = aⁿ`.
- `resolvent_laplace` / `laplace_resolvent_shift` — `∫₀^∞ e^{−ct}dt = 1/c`, and the paper's
  displayed termwise step `∫₀^∞ e^{−(1+u)t}e^{−γ²t}dt = 1/(u+1+γ²)`, the identity by which
  uniqueness of the Laplace transform converts the Hadamard partial-fraction sum into the
  heat expansion.
- `subordination_at_zero` — the `x = 0` case of the paper's boxed subordination formula,
  `∫₀^∞ e^{−r²t}(4πt)^{-1/2}dt = 1/(2r)`, via the `a = 1/2` Gamma integral and `Γ(1/2)=√π`.
- **`primeSide_heatGaussian` — the bridge to Thread L.** The paper's arithmetic sum
  `Σ_n Λ(n)n^{-1/2}e^{−(log n)²/(4t)}` is *exactly half* of `GppWeilLadder.primeSide` at the
  heat Gaussian, because that test function is even. **The new paper's prime side is the
  Weil support ladder's prime side** — so `primeSide_eq_truncation`,
  `primeSide_eq_zero_of_support_lt_log_two` and the rest of Thread L apply to it verbatim.
  This is the payoff of the thread: two independent programmes land on one formal object.

Anchors verified at the pin by reading pinned source (loogle deliberately not trusted):
`Real.integral_rpow_mul_exp_neg_mul_Ioi` (Gamma/Basic:474), `Real.Gamma_one_half_eq`
(GaussianIntegral:332), `Real.sqrt_sq` (Data/Real/Sqrt:160), `Real.sqrt_mul` (ibid.:302),
`iteratedDeriv_exp_const_mul` (ExpDeriv:366).

**Pin lesson recorded:** `iteratedDeriv_exp_const_mul` is in the **root** namespace, not
`Real` — it is declared under `open Real in` *after* `end Real`. Writing
`Real.iteratedDeriv_exp_const_mul` gives "unknown constant". This is the same class of trap
as the loogle pin-mismatch lesson: grep finding a name in a file does not tell you its
namespace. Also re-confirmed: `field_simp` can close a goal outright, leaving a trailing
`ring` to error "no goals".

**NOT claimed, and named precisely:**
1. **General-`x` subordination**, `e^{−rx}/(2r) = ∫₀^∞ e^{−r²t}(4πt)^{-1/2}e^{−x²/(4t)}dt`.
   Only `x = 0` is proved. The general case is the classical
   `∫₀^∞ e^{−at−b/t}t^{-1/2}dt = √(π/a)e^{−2√(ab)}` — a `K_{1/2}` Bessel evaluation, **not in
   Mathlib at the pin** (searched). Needs the Glasser-type substitution
   `u = √(at) − √(b/t)`. That is its own thread, not a corollary. **This is the single
   highest-value next target in Thread HT** — it is self-contained real analysis with no
   arithmetic input, and it is the engine of the paper's entire reformulation.
2. **Bernstein's theorem** (completely monotone ⟺ Laplace transform of a positive measure).
   Absent from Mathlib. The paper's `(2)⇒(3)⇒(1)` direction rests on it.
3. **The heat-trace criterion itself.** The forward direction needs the centered Hadamard
   product for `ξ` plus zero-counting — the same missing infrastructure that blocks the RH
   thread repo-wide regardless of reformulation, as recorded in the mining plan.

*Audit against the corpus root-error pattern (`memory.context.rh_corpus_root_error_pattern`):
this reformulation does **not** reproduce it. The fatal pattern is treating a zero ordinate
as a genuine point-spectrum eigenvalue of the scaling generator with `E_A({t₀}) ≠ 0` — false
unconditionally, Lean-proved in `MomentumGeneratorNoPointSpectrum.lean`. The heat-trace route
never asserts a spectral atom: it asks for complete monotonicity of an explicit
zero-independent arithmetic function, a classical real-analysis property, and gets its
measure from Bernstein rather than from a spectral projection. The open content sits in
Bernstein's hypothesis, not in a false eigenvalue claim. Clean on this axis.*

**General-`x` subordination — DONE.** `GppHeatTrace.subordination_general`, kernel-verified
to `[propext, Classical.choice, Quot.sound]` only, **no Bessel-function machinery used**
(none exists in Mathlib at the pin). Proved via: `t=(√b/√a)w²` reduces the target to
`auxK(c):=∫₀^∞e^{-c(w²+1/w²)}dw = (1/2)√(π/c)e^{-2c}`; the `w↦1/w` symmetry
(`integral_comp_rpow_Ioi`, p=-1) gives `2·auxK(c)=∫₀^∞(1+w^{-2})e^{-c(w²+1/w²)}dw`; the
substitution `p=w-1/w` (a genuine bijection `(0,∞)→ℝ`, derivative exactly `1+w^{-2}`) turns
this into `e^{-2c}∫_ℝe^{-cp²}dp` via `integral_image_eq_integral_abs_deriv_smul`, with
surjectivity of `w-1/w` onto `ℝ` closed by `IsPreconnected.intermediate_value_Ioi`/`_Iio` on
`Ioi 0`; `Real.integral_gaussian` closes the final Gaussian step. Two pin-specific pitfalls
hit and recorded: (1) `set`-bound local values (`set k := ... with hkdef`) can be silently
unfolded back by `field_simp`/`ring` mid-proof, defeating a deliberate `k → √k·√k`
substitution — fixed by `clear_value` to sever the `let`-transparency once the defining
equations are extracted; (2) `Mathlib.MeasureTheory.Integral.ExpDecay`'s
`integrable_of_isBigO_exp_neg`, when given a hand-built `ContinuousOn` term via
`.comp`/`.continuousOn`, can hit a genuine `isDefEq` timeout (confirmed not to resolve even
at 5× the default heartbeat budget) — resolved by using the more specific
`exp_neg_integrableOn_Ioi` directly wherever the dominating function is literally
`exp(-(c·x))`, sidestepping the problematic unification entirely.

**Full-paper survey (this session):** `GppVerify/ThreadHT/ARITHMETIC_PRINCIPAL_SERIES_SURVEY.md`
indexes and classifies **all 102** theorem-level environments in the source `.tex`, per the
standing instruction to account for everything in it. Result: ~99 depend on paper-private
apparatus (the BPY law, four-field Euclidean fields, Wigner–Born distributions,
Thorin–Stieltjes representations, Möbius–Koszul complexes, Hardy defect spaces, Cayley
atlases, prime–Archimedean Gram matrices, causal-commutator algebras) — formalizing any one
would be its own multi-file thread, comparable in scope to Thread S's `SignatureInertia.lean`
foundation, not an incremental addition. Two more elementary pieces were extracted and
proved this session: `archimedeanLaplace_aux_one`/`_two` in `HeatTraceCriterion.lean`, the
purely exponential-integral half of the paper's "Exact Archimedean Laplace transform"
theorem (its third piece needs digamma, **confirmed entirely absent from Mathlib at the
pin** — not even the function itself exists, a separate large undertaking). The paper's own
Conclusion was read in full: it ends "No proof of global trace conservation or positivity is
supplied here. Therefore no proof of RH is claimed" — consistent, word for word in spirit,
with everything already found in this repo's corpus-error audits.

## Thread Weil-Parity — the exact semilocal Weil form / prime–Archimedean Gram matrix

**Status: one closed-form calculus fact proved (`archimedean_diagonal_tail`). Everything
else about this thread is open, numerical-evidence-only research — not close to formal.**

From `arithmetic_principal_series_RH_program34.tex`, "The exact semilocal Weil form"
(~line 6414): the finite prime–Archimedean Gram matrix `Q_{λ,N}` — the object flagged
but not investigated in the Thread HT writeup above. This session opened it via a
numerical checkpoint (not a Lean proof attempt) implementing the exact construction and
comparing observed eigenvalue parity splits against a derived pure-prolate asymptotic
(Connes–Consani prolate-function route). `lean_results` rows `09e24660…`, `02a84cc3…`,
`079ca52f…` record the checkpoint in full; summary:

- The paper's `W_ℝ♯` (Archimedean piece of `Ψ♯`) integrates `[u^{1/2}F(u) − F(1)]/(u−u⁻¹)`
  over `[1,∞)`. A first numerical pass truncated this at the support boundary and produced
  a spurious negative scalar "floor" in the raw eigenvalues.
- The bug was diagnosed exactly: for the diagonal case (`F(1)=2`, `F` supported in
  `[1,c]`), the omitted tail is `−2∫_c^∞ du/(u²−1) = −log((c+1)/(c−1))`. Restoring it
  reconciles the computation with Connes–Consani's published tiny positive minima.
- **`archimedean_diagonal_tail` in `ThreadWeilParity/ArchimedeanTail.lean` promotes this
  closed form to an actual Lean theorem**, proved from Mathlib's elementary calculus +
  `integral_Ioi_of_hasDerivAt_of_nonneg'` (FTC-2 on `(a,∞)`), kernel-verified to Lean
  built-ins only. This is a real, if small, contribution: the numerical fix used an
  identity that was correct but unproved; now it is proved.
- **Not attempted, and not close to formalizable**: the observed odd/even parity ratio
  `δ₋/δ₊` (numerically in the hundreds and growing with `N`), the derived pure-prolate
  asymptotic ratio `~(1408π²/195)λ⁴` from Fuchs's fixed-mode asymptotic, and — most
  importantly — the theorem that would connect them: a "second-cancellation/double-defect
  factorization" making the finite-Galerkin transfer error `O(1−χ)` rather than
  `O(√(1−χ))`, which the checkpoint explicitly names as **required and not yet derived,
  even informally on paper**. This is genuinely open research, not a formalization gap —
  there is no classical proof to formalize yet. Per standing discipline, no axiom stands
  in for it and no shortcut was taken to manufacture a compiling theorem; it is named here
  honestly as the exact remaining boundary. Next source target named in the checkpoint:
  the Connes–Consani archimedean Weil/prolate Selecta construction. No RH claim anywhere
  in this thread.

### `public.formalization_queue` — the canonical ChatGPT→Lean handoff (2026-08-15)

Daniel introduced a dedicated Supabase table, `public.formalization_queue`, as the
canonical research-to-formalization handoff for this thread going forward — read it (not
just `lean_results`) at the start of every Weil-Parity session, oldest-`ready`-first by
priority. Two flagship items formalized this pass, both in
`GppVerify/ThreadWeilParity/CrossResolvent.lean`, both **PROVED unconditionally**, both
kernel-clean, no axiom, no sorry:

- **`cross_resolvent_det_identity`** (queue item `3ebed50a`, the item explicitly marked
  "start here"). Coordinate/Schur-complement form of the parity displacement determinant
  identity: for the even block `A` in `Unit ⊕ n` block form and the odd block
  `B = E − βη'ᵀ` that the Sylvester relation `CA − BC = βη'ᵀ` forces, `det(B−zI) =
  det(A−zI) · η((A−zI)⁻¹e0)`. Proved via `Matrix.det_fromBlocks₂₂` (Schur complement) for
  `det(A−zI)` and `Matrix.det_add_mul` (the Matrix determinant lemma) for `det(B−zI)` as a
  rank-one update of the same Schur block, then solving `(A−zI)x = e0` explicitly and
  substituting. This is the coordinatized reduction of the abstract statement (arbitrary
  `V`, `W`, surjective `C` with `ker C = span{e0}`) — choosing a basis adapted to `ker C`
  is exactly what those hypotheses force, so the coordinate form carries the full content.
- **`parity_crossing_obstruction`** (queue item `0cf9aebf`). If `C A₊ − A₋C = βηᴴ` and
  `λ` is a common eigenvalue of Hermitian `A₊` (eigenvector `e`) and `A₋` (nonzero
  eigenvector `o`), then `⟪o,β⟫·⟪η,e⟫ = 0`. Proved via a short self-adjoint pairing
  argument (`hermitian_dotProduct_mulVec`: for Hermitian `M` with `M·x=μx`,
  `⟪x,Mv⟫=conj(μ)⟪x,v⟫`), applied to the Sylvester relation evaluated at `e` and paired
  against `o`. Only `A₋` Hermitian is actually used by the proof (kept `A₊` Hermitian as a
  hypothesis for fidelity to the queue item's physical setup).

Both were developed by writing Lean directly against the queue's stated hypotheses and
iterating on compiler feedback — per Daniel's explicit instruction this pass, no
by-hand pre-verification gate was inserted before attempting the formalization; Lean
itself was the check. Neither needed correction: both compiled to the exact statement as
queued.

**Third item, same pass, in `ThreadWeilParity/OddEigenpairLift.lean`** — queue item
`c0c96bbc`, "Odd eigenpair canonical lift and Schur-Rayleigh defect identity", building
directly on `CrossResolvent.lean`'s block structure and Schur-complement scalar (there
`s`, here `φ`). Three theorems, all **PROVED**, kernel-clean:

- `odd_eigenpair_defect_step1`: `(E-λI)x1 = s•b` (`s := η1ᴴx1`), from the Sylvester
  relation applied at an `Aminus`-eigenvector `(λ,y)`, `x1 := D⁻¹y`.
- `odd_eigenpair_defect_step2`: `x1 = s•(E-λI)⁻¹b` when `E-λI` is invertible.
- `odd_eigenpair_canonical_lift`: the canonical lift `x := s•(-1,(E-λI)⁻¹b)` satisfies
  `η*x=0` and `(Aplus-λI)x = -s·φ(λ)·e0`. **Carries one extra explicit hypothesis**,
  `hw1 : η1ᴴ((E-λI)⁻¹b) = 1`, that the queue item's prose doesn't name separately — it
  is not a free assumption about arbitrary `b,η1,E,λ`; combining steps 1+2 forces it
  automatically whenever `s≠0` (divide `s=η1ᴴx1=η1ᴴ(s•(E-λI)⁻¹b)=s·(η1ᴴ(E-λI)⁻¹b)` by
  `s`). It's a genuine solvability/quantization condition on `λ`, stated explicitly per
  standing discipline rather than silently assumed. The item's closing Rayleigh-quotient
  remark (`⟪x,(Aplus-λI)x⟫=|s|²φ(λ)`) is definitionally the same content as the second
  conjunct paired against `x`, so it is not restated as a separate theorem.

**Not attempted this pass, and why**: the remaining `A. WEIL-PARITY CORE` queue items
(`Positive residues imply strict interlacing`, `Positive commuting metric equivalent to
residue positivity`, the two cross-resolvent/cross-heat positivity items, `Continuation
of even ground`) build on these three and are the natural next targets — genuinely
tractable with the same toolkit, just not reached this session. `Positive residues
implies strict interlacing` in particular is a substantially larger lift than the three
proved so far: it needs a genuine spectral decomposition of the resolvent
(`η*(A-zI)⁻¹e0 = Σⱼ cⱼ/(αⱼ-z)`) plus real-analysis machinery (monotonicity, IVT) that
none of this session's algebraic block-matrix work required.
The `C`/`D` sections (Singular Pick/Nevanlinna kernel theory, Suzuki self-adjoint
extensions, Herglotz/Vitali convergence) require entire theories absent from Mathlib at
this pin (no Pick interpolation, no deficiency-index self-adjoint extension theory, no
Herglotz function machinery) — these are multi-session undertakings on their own, not
attempted here.

**Standing warning, from `research_notes` (`35a9efdc…`), that must travel with every use
of these two theorems**: a stress test of the exact reconstructed CCM matrix found a
counterexample to global residue positivity — at `c=13,N=6` the top cross-resolvent
residue is negative (`≈ −1.71×10⁻²`), so there is **no** universally positive commuting
metric for the real arithmetic object. `cross_resolvent_det_identity` and
`parity_crossing_obstruction` are real, unconditional, abstract theorems about *any*
operator pencil satisfying their stated hypotheses — but the actual finite CCM Weil
matrix is not known to satisfy the positivity hypotheses the downstream queue items
(`Positive residues imply strict interlacing`, etc.) would need to say anything about its
real spectrum. Nothing proved this session is a step toward RH.

## Thread Tree-Loop-Sewing — tree-to-loop topology behind the shadow-discontinuity program

**Status: graph-combinatorics layer PROVED unconditionally; the analytic celestial-sewing
identity is isolated as a named local hypothesis, not proved, not hidden.**

From Toupin, *Loop Integrands Hidden in Trees: Explicit Extraction by Double Shadow
Discontinuities* (Aug.\ 2026), delivered as a handoff package
(`GPPVERIFY_TREE_LOOP_HANDOFF.md` + `GppTreeLoopSewing.lean` draft). The paper's central
claim: a higher-point *tree* celestial correlator's shadow-pole analytic structure already
encodes a lower-point loop *integrand*, extractable by a double shadow discontinuity
`dDisc_sh^(56) := Disc^sh_6 ∘ Disc^sh_5`. Landed in new file
`GppVerify/CelestialHolography/TreeLoopSewing.lean`, commit `<pending>`.

- **Graph-combinatorics (PROVED, unconditional, all `L`).** `pairSewing_cycleRank`: a
  connected cubic tree with `4+2L` external leaves, after sewing `L` disjoint pairs of the
  extra `2L` leaves, is a connected 4-point graph of cycle rank exactly `L`. This corrects
  an earlier draft's "L+1 shadow closures" language — closing `L` disjoint pairs is `L`
  pair sewings, not `L+1`; the handoff doc and the paper's own v18 both make this
  correction explicit. `sixPoint_onePair_oneLoop_counts` specializes to the one-loop box
  (6-point tree, one pair sewing → cycle rank 1). `boxDenominator_is_pairClosure`: the
  closed box denominator is definitionally the missing closure edge `Q(ℓ)` times the three
  denominators already present in the open six-point chain. All proved by direct
  `omega`/`norm_num` computation on the vertex/edge/leg counts — no graph object is
  constructed, only its counts, which is exactly what the paper's topology theorem claims
  and no more.
- **Analytic interface (NOT proved, correctly isolated).** The paper's own boxed
  "remaining analytic theorem" — `𝓜⁻¹_{5,6}[dDisc_sh^(56) T̃₆] = (i/(ℓ²+i0)) T₆(...)` —
  is represented by `ShadowPairSewing.sewing_identity`, a field of a local structure, not
  a global axiom and not a stub. `ShadowPairSewing.tree_to_loop_extraction` is the
  (structurally immediate) corollary that the pipeline commutes, conditional on that one
  named hypothesis via an instance argument. Nothing here proves `sewing_identity` for an
  explicit six-point celestial amplitude — the paper itself states the exact
  normalization/sign/prescription must be derived from actual celestial conventions, not
  inserted because it is the target.
- **Does NOT touch the existing `GppShadowDisc` stubs.** `celestial_amplitude_has_cut`,
  `disc_equals_loop_integrand`, `shadow_disc_mellin_density` in
  `CelestialHolography/ShadowDiscontinuity.lean` remain exactly as they were —
  `theorem foo : True := trivial` stubs (confirmed by re-reading the file, not axioms
  despite the handoff doc's looser "infrastructure assumptions" language). This thread
  does not discharge, replace, or duplicate them; per the handoff's explicit instruction,
  they are left untouched until an explicit six-point sewing identity is actually proved.
- **Blueprint correction, same pass.** While adding this thread's blueprint chapter,
  re-audited the pre-existing `thm:shadow-discontinuity` entry and found it read as more
  proved than it is: `GppShadowDisc.shadow_discontinuity` is itself a `True`-stub, and the
  blueprint's "Proved clean" bullet list actually names four *ingredient* lemmas (complex
  discontinuity formula, shadow involution, shadow-conjugate identity, simple-pole
  residue), not a proof of the boxed claim. Added an explicit correction note in the
  blueprint chapter rather than silently leaving the stronger-sounding original wording.
- **Not attempted / out of scope for GPPVerify:** the handoff's item 9 (update the LaTeX
  paper to the corrected `L` pair-sewing count) — the paper source is not part of any repo
  in this session's scope; only the Lean/blueprint side was actioned.

## Thread S — the signature/inertia route (August 2026 Anthropic result)

**Status: STEP 0/2 DONE, STEP 1 FOUNDATION ONLY — far from S1, nowhere near S2-S4.**
`GppVerify/ThreadS/{SOURCES.md, MATHLIB_RECON.md, SignatureInertia.lean}`.

Source verified real (not a fabrication, not a memory-cutoff hallucination — confirmed by
web search and direct download): Claude/Anthropic, *"More than two thirds of the zeros of
the Riemann zeta function are simple and on the critical line"*, dated 2026-08-11.
**Unconditional.** Raises the proven lower bound on zeros that are simple and on the
critical line from 5/12 to 2/3 (indicator window) / `2 − c_MT⁻¹ = 0.67250…` (optimal
Montgomery–Taylor window, `c_MT⁻¹ := (1/2)cot(1/√2) + 1/√2`, symbolic — never hardcode the
decimal). Own Lean artifact (`github.com/anthropics/zeta-23-lean`, Apache 2.0, no custom
axiom, no sorry in the main library) already exists, at a **newer** pin (Lean v4.33.0-rc2,
Mathlib `51e6992e`) than GPPVerify's own (`c44e0c8`) — not ported here, both because of the
pin gap and because copying it would add nothing GPPVerify doesn't already have by reading
it directly. See `SOURCES.md` for the full source audit.

**The RED-ALERT replacement lemma, resolved and named:** the paper's own text states it
plainly — "RH entered only to read the zero side termwise as a positive sum over real
ordinates." The replacement: truncate Weil's Hermitian form, decompose `G̃ = P + Q`
(on-line zeros → rank-one positive blocks in `P`; off-line pairs → signature-(1,1) blocks
in `Q`, Bombieri 2000's observation), and combine a Hilbert–Schmidt second-moment bound on
`n₊(Q)` with the rank–trace inequality `rank P1 ≥ 2 tr P1 + 4 tr Q' − 4b − ‖P1+Q'‖²_HS`
(the paper's Lemma 3.2) — never assuming `n₊(Q)=0`. **This inequality is Thread S's actual
target and is not yet formalized here.**

`SignatureInertia.lean` has exactly one theorem: `inertia_sum`,
`nPos hQ + nNeg hQ + nZero hQ = Fintype.card n` for `Q : Matrix n n ℂ` Hermitian, via
`Matrix.IsHermitian.eigenvalues : n → ℝ` (indexed directly by `n` at the pin — no extra
reindexing needed) and a trichotomy partition of `Finset.univ`, using
`Finset.filter_card_add_filter_neg_card_eq_card` twice. Kernel-clean.

`MATHLIB_RECON.md` records what GPPVerify's own pin has: `Matrix.IsHermitian.eigenvalues`/
`eigenvectorBasis`/`spectral_theorem` (Spectrum.lean), `Matrix.PosSemidef`/`PosDef` with a
bridge to `QuadraticForm ℝ` (PosDef.lean), and — genuinely useful — **Sylvester's law of
inertia already exists for real quadratic forms** (`QuadraticForm/Real.lean`,
`equivalent_one_neg_one_weighted_sum_squared` etc.), reachable from the Hermitian case via
realification, so Step 5 (congruence invariance) is not a from-scratch reconstruction of
Sylvester's theorem — it is a bridge to an existing one. Confirmed absent: any Hermitian
"inertia"/"signature"/"congruence" concept, and the rank–trace inequality itself (searched;
not of this shape anywhere in the pinned tree).

**NOT done, stated plainly rather than implied:** the subspace-dimension bounds
(`dim_le_nPos_of_posDef_on`/`dim_le_nNeg_of_negDef_on`), congruence invariance
(`inertia_congruent`), the rank–trace inequality (the actual payload), the finite
zero-configuration instantiation with named analytic hypotheses H0–H5, the bridge to
`WeilPositivityCriterion.lean`/`CauchyKernelPositive.lean`, and the falsification harness.
This is Step 1's first theorem only — a foundation, not a milestone. No claim of RH, no
claim of reproducing Anthropic's result, is made or implied by anything in this section.

## The third category: `True := trivial` stubs — documented but untracked

Beyond `sorry` (zero) and `axiom` (16 declarations), the tree carries **~131
`theorem foo : True := trivial` stubs across 25 files**. The README documents this
convention explicitly and it is the *right* call — parking an open result as a vacuous
statement with a doc comment naming the upstream gap is strictly more honest than an `axiom`
asserting the open claim.

The gap is that it is **not tracked**. A file full of stubs still reports `0 sorry / 0 axiom`
and reads as clean; `#print axioms` on a stub returns a spotless list. Densest files:
`HaarPositivityWeil`, `QuantumGravity/WightmanAxioms`, `NumberTheory/ShadowEulerIdentity`
(12 each), `CelestialHolography/TwistorGoogly` (11), `YangMills/MassGap` and
`StandardModel/MajoranaCondition` (10 each).

Two concrete follow-ups, both small:
1. **Report the stub count wherever the sorry/axiom count is reported** — README table gets a
   third column; any status claim quotes all three numbers.
2. **Make CI actually gate.** `build.yml`'s "Sorry count" step ends in `|| true` and only
   *prints* — it cannot fail. It should fail the build on any `sorry`, and print (not fail)
   a stub census so drift is visible in every run.

*Retire a stub only by proving it. Deleting it, or weakening its statement while keeping its
name, is the one move that would make this tree dishonest.*

---

## Thread QG-Blackbody — Stefan–Boltzmann family, Gamma-modulus identity, all-loop finiteness

**Status: DONE (this session), three new theorems, kernel-clean, no axiom, no sorry.**
From a fresh upload of `haar_qg_paper_v215.tex` ("On Self-Dual Measure and Finite Quantum
Gravity"), `kinematic_block_v1.tex`, and the capstone `blackbody_law_qg_dtoupin_v1.tex`, with
companion scripts `verify_qg_measure.py` / `verify_qg_kinematics.py` /
`verify_blackbody_capstone.py`. Earlier drafts of the first two papers
(`haar_qg_paper_v2151.tex`, `kinematic_block_v11.tex`) were already the source for Thread S
(`SinhZetaBridge.lean`, `M₁ = 1/8`) and Thread E (`M₂ = 1/90`) — this pass covers three
genuinely new results the new drafts add, checked directly against the live tree (grepped for
`Plancherel`/`conical`/`Legendre`/`Mehler`/`Temperedness` before starting; none of that
kinematic-block/conical-function material existed yet).

* **`QuantumGravity/StefanBoltzmannFamily.lean`** — `stefan_boltzmann_family`: the general
  moment `m_s = π^{-(s+1)}(1-2^{-(s+1)})Γ(s+1)ζ(s+1)` for **every real `s > 0`** (T7 of the
  capstone script), not merely the sampled `s = 1, 2, 3, 1.37`. Proved by a `π`-substitution
  (`integral_comp_mul_left_Ioi`) reducing to `SinhZetaBridge.sinh_mellin_zeta` at exponent
  `s+1`. Corollaries `m_one_eq` (`= 1/8`) and `m_three_eq` (`= 1/16`, the capstone's T7'').
* **`QuantumGravity/GammaModulusIdentity.lean`** — `gamma_one_add_mul_gamma_one_sub`:
  `Γ(1+iλ)Γ(1-iλ) = πλ/sinh(πλ)` exactly (T2/T4 of the capstone), via Euler's reflection
  formula (`Complex.Gamma_mul_Gamma_one_sub`, unconditional) shifted by one factor of `iλ`
  and `Complex.sin_mul_I` turning the denominator into `sinh(πλ)·i`.
* **`QuantumGravity/AllLoopFiniteness.lean`** — **`GppAllLoopFiniteness.finiteness`**: for
  every loop order `L ≥ 1`, `0 < 𝓜_L ≤ (1/8)^L` (`thm:finiteness`, the paper's own central new
  claim — the all-loop bound the Python script only spot-checks at `L=1`). The `L`-fold
  `ℝ_{>0}^L` integral is encoded via its own Fubini/Tonelli iterated-integral expansion — a
  recursive chain kernel `K n` (`K 0 = P⁺`, `K (n+1) λ = P⁺(λ)·∫⁻μ, K n μ·P⁺(|μ-λ|)`) — rather
  than general `Fin L`-indexed product-measure machinery. Carried entirely in `ℝ≥0∞`
  (`lintegral`), which makes Tonelli and monotonicity *unconditional*: no integrability side
  conditions had to be threaded by hand anywhere in the induction, since the paper's own proof
  (bound each rung `P(|λⱼ-λⱼ₊₁|) ≤ 1`, discard it, factorize what remains) is exactly a
  positivity argument. Positivity `0 < 𝓜_L` is carried as the stronger pointwise-everywhere
  invariant `∀λ>0, 0<K n λ`, closed via `lintegral_pos_iff_support` on an explicit
  λ-avoiding subset. Proved for **every** `L` at once by induction — not merely instantiated
  at small `L`.

**Honest boundary — NOT done, named plainly:** the rationality/PSLQ program beyond `M₁,M₂`
(the paper's `M₃ = 1/16` numeric value is now *implied* by `m_three_eq` above, but the
paper's own three-loop closed-form derivation via 44-digit PSLQ relation-hunting is not
formalized, nor is `M₂`'s independent re-derivation via this family's `s=2` — only `L=1,3`
were needed for cross-checks here); the Wiener–Hopf/Parseval odd-zeta cancellation and
wall-count combinatorics; the **entire kinematic-block/conical-function program**
(`kinematic_block_v1.tex` Theorems 2.1, 3.1, 4.1, 4.4, the Mehler–Fock pair, the `Δ=2s`
dictionary — none of this exists in the tree, and Mathlib's support for conical/Legendre
functions is thin enough that scoping it is a separate task, not started); and most of the
blackbody capstone's remaining structural theorems (T1 triple equality, T3 logistic
characteristic function, T5 cumulant law, T6 Matsubara residues, T13 Fourier/Kirchhoff pair,
T14) beyond the two (T2, T7-family) landed here.

---

*History: earlier arcs (p-adic Tate thread PRs #44–58, Cesàro/Abel/Yakaboylu elementary
layer PRs #59–64) predate this document; see git log. Thread completions are recorded
here as they merge.*
