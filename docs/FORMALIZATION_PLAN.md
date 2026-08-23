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

## Thread GP — the positive Gamma--Plancherel defect

**Status: PARTIAL, WITH AN EXACT INFINITE SUBFAMILY —
`RiemannHypothesis/GammaPlancherelDefect.lean`, kernel-clean, no new axiom, no sorry.**

Source: `arithmetic_principal_series_RH_program-34.tex`, Theorem 62.1.  For `q,a,b>0`
the paper defines the four-term real-place logarithmic-derivative defect

`D_q(a,b)=g_infinity(q+a)+g_infinity(q+b)-g_infinity(q)-g_infinity(q+a+b)`

and identifies it with

`integral_0^infinity e^{-qx}/(1-e^{-2x})(1-e^{-ax})(1-e^{-bx}) dx`.

The new module proves the following unconditional layer:

- `density_eq_spectralWeight`: the exact pointwise identity
  `e^{-qx}/(1-e^{-2x}) = e^{-(q-1)x} P(x/pi)/(2x)` for `x>0`, where
  `P(lam)=pi*lam/sinh(pi*lam)` is the repo's existing celestial cut weight.  Thus the
  paper's Gamma defect and the QG spectral-weight thread meet at one formal object.
- `pointwise_gram_nonneg`: after multiplying by the two real features
  `1-e^{-ax}`, the kernel at each `x>0` is rank one, so every complex finite Gram form is
  nonnegative.  `integral_gram_nonneg` proves that integration preserves this positivity
  under explicit pairwise integrability; `truncatedDefectKernel_gram_nonneg` discharges
  those hypotheses automatically on every compact interval `[eps,R]`, `eps>0`.
- A stronger exact slice avoids the missing general digamma integral representation.
  For `q>0`, `a=2m`, `b=2n` with `m,n:Nat`, `digamma_add_nat` iterates the already proved
  `GppDigamma.digamma_add_one`; the denominator cancels by a finite geometric sum.  This
  yields, in Lean,

  `D_q(2m,2n) = integral_0^infinity defectIntegrand q (2m) (2n)`

  `             = sum_{k<n} (1/(q+2k)-1/(q+2m+2k))`.

  The finite exponential decomposition proves full integrability before evaluation by
  `GppHeatTrace.resolvent_laplace`.  The final resolvent difference is nonnegative and is
  strictly positive for `m,n>0`.  `gammaDefect_even_gram_nonneg` proves the actual
  four-term Gamma defect is positive semidefinite on every finite collection of
  even-natural shifts — not merely the integral kernel under a hypothesis.

**Precise open boundary.**  For arbitrary positive real `a,b`, identifying the integral
with `D_q(a,b)` still needs the general real digamma difference/integral representation.
Mathlib has differentiability of `Real.Gamma`, and the repo defines `GppDigamma`, but the
required integral representation is not upstream at this pin.  No arbitrary-real equality,
global trace conservation, RH criterion, or RH consequence is claimed here.  The lattice
result is an exact infinite subfamily of Theorem 62.1 and a clean base for the general
analytic bridge.

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

### Follow-up, 2026-08-17: dispersion reconstruction attacks `sewing_identity` directly

**Status: the general Sokhotski–Plemelj mechanism is now proved unconditionally; the
celestial specialization to the actual six-point tree is still open, but the gap is now
three named analytic hypotheses instead of one opaque one.**

Triggered by a fresh handoff bundling four connected papers (shadow-discontinuity/tree-
to-loop, Haar/QG measure `haar_qg_paper_v215.tex`, kinematic-block, blackbody) and an
explicit instruction to attack `ShadowPairSewing.sewing_identity` head-on rather than
narrate around it. Read all four papers and re-audited `TreeLoopSewing.lean`,
`ShadowDiscontinuity.lean`, `MellinKinematics.lean`, and the three QG-Blackbody files
directly against `main` (commit `0a53705`) before starting — everything matched the
existing docs exactly, no drift found. Also checked `public.formalization_queue` (27
rows, all Weil-Parity/Suzuki-Herglotz/Prime-* threads — nothing on celestial holography)
and `public.research_notes`/`lean_results` for anything newer or contradicting on this
thread — found none; `eb6d17f0…` (the original Tree-Loop-Sewing landing) is the latest
record and matches the repo state exactly.

**New file: `GppVerify/CelestialHolography/DispersionReconstruction.lean`.** The paper's
own Step 6 (`haar_qg_paper_v215.tex`, Theorem `thm:shadow-disc`) invokes cut-
constructibility to go from "the shadow discontinuity is the unitarity cut" to "the loop
integrand is reconstructed," without deriving the actual mechanism — precisely the gap
the task singled out: a discontinuity naturally gives on-shell support like `δ⁺(q²)`,
while the loop integrand needs `1/(q²+i0)`. This file proves the general, physics-
convention-independent complex-analysis fact that supplies that mechanism (the algebraic
core of Sokhotski–Plemelj), **unconditional, two theorems, both kernel-clean** (`#print
axioms` shows Lean built-ins only):

- `lorentzian_jump`: the exact finite-`ε` identity
  `1/((x-z₀)+iε) - 1/((x-z₀)-iε) = -2iε/((x-z₀)²+ε²)` — no limiting procedure, no
  distributions, pure algebra (`div_sub_div` + a `linear_combination` against
  `Complex.I_sq` for the denominator product).
- `lorentzian_kernel_tendsto_zero_off_pole`: the regulated kernel vanishes pointwise away
  from the pole as `ε→0⁺` (via `Continuous.div` + evaluating at `ε=0`).

**Numerically checked first** (`verify_dispersion.py`, mpmath, 40 dps): (1) the exact
Lorentzian jump identity at several `(z₀,ε,x)`, machine-zero residual; (2) the classical
`ε→0` dispersion-integral reconstruction of a toy simple-pole propagator `F(z)=R/(z-z₀)`
from its own regulated discontinuity, confirming the reconstruction error shrinks with
`ε` as expected — this is the general mechanism, explicitly *not* a celestial
calculation, and explicitly *not* a reparametrized Feynman integral (the `box_shadow_1d`
mistake the task warned against).

**What this does and does not do to `sewing_identity`.** It reduces the opaque hypothesis
to three named, checkable analytic properties of the actual six-point celestial tree,
stated in the module doc and mirrored in the blueprint
(`sec:dispersion-reconstruction`): **(H1) meromorphy** of the pair-sewn spectral object
in `ℓ²` with only a simple pole at `ℓ²=0`; **(H2) decay** at infinity sufficient to close
the dispersion contour; **(H3) residue match** — the shadow-pair-OPE discontinuity (the
existing Steps 1–5) has residue exactly `-2πi·T₆(ℓ,p₁,…,p₄,-ℓ)` at `ℓ²=0`. **None of
H1–H3 is established for the actual `(z,z̄)`-dependent celestial amplitude this session**
— that remains the open boundary every paper in this program already names. This file
does **not** discharge `sewing_identity`, does not touch any `GppShadowDisc` stub, and
does not prove the mass-normalization half of Sokhotski–Plemelj
(`∫ε/((x-z₀)²+ε²)dx = π`, reducible to Mathlib's `integral_univ_inv_one_add_sq` by an
affine substitution) — named honestly as a gap since the needed translation-invariance-
of-Lebesgue-measure lemma wasn't chased down this pass, not forced with a `sorry`.

**Graph-layer strengthening (item A/B/C of the handoff's Lean tasks): scoped, not
attempted.** Searched Mathlib's `SimpleGraph.Acyclic` for the anchor needed to upgrade
`cubicTreeVertices`/`cubicTreeInternalEdges` from definitions to theorems about an actual
graph: found `SimpleGraph.IsTree.card_edgeFinset : G.edgeFinset.card + 1 =
Fintype.card V` (general tree edge-count formula, `Combinatorics/SimpleGraph/
Acyclic.lean:152`) as the correct starting anchor for "one sewing raises cycle rank by
one" (add an edge between two non-adjacent tree vertices via `T ⊔ SimpleGraph.fromEdgeSet
{s(a,b)}`, show it stays connected and gains exactly one edge). Did not attempt the
proof itself this pass — the harder, un-anchored part is the cubic/trivalent-vertex
leaf-count combinatorics (`n` leaves ⟹ `n-2` trivalent vertices), which needs a
handshake-lemma-style degree-sum argument with no direct Mathlib anchor found yet, and
attempting a rushed partial `SimpleGraph` proof under time pressure risked exactly the
"no half-finished implementations" failure mode. Left as a concretely scoped next step
(anchor lemma named) rather than a guess.

**Structural finding, same pass (paper-level, NOT yet Lean, NOT a Lean gap): the naive
per-diagram energy Mellin transform of the comb ordering does not exhibit the claimed
joint shadow pole.** Attacking "the shadow pole must be derived, not assumed" directly
for the exact comb tree used throughout this thread (vertices A–B–C–D; legs `(5,1)` at
`A`, `2` at `B`, `3` at `C`, `(4,6)` at `D` — the ordering `openSixPointChainDenominator`
formalizes, chosen because *closing* legs 5,6 gives the box). Checked symbolically
(`check_comb_factorization.py`, sympy, not committed — same convention as the other
companion scripts) which propagator denominators depend on which of `ω5, ω6`: using
overall momentum conservation to rewrite the third denominator as `(k5+p1+p2+p3)² =
-(p4+k6)² = 2p4·k6`, the three denominators are `D1 ∝ ω5`, `D2` linear in `ω5` (at fixed
`ω1,ω2`), `D3 ∝ ω6` (at fixed `ω4`) — **`D1,D2` never depend on `ω6` and `D3` never
depends on `ω5`, confirmed symbolically.** Consequently
`∫dω5 dω6 ω5^{Δ5-1}ω6^{Δ6-1}/(D1D2D3)` factorizes exactly into a product of two
*independent* 1D Mellin transforms, one in `Δ5` alone, one in `Δ6` alone — each a bare
power-law integral over `(0,∞)`, whose standard regularization is a delta function
fixing that single leg's own dimension (`Mellin[1](λ)=2πδ(λ)`, i.e. `D3` alone forces
`Δ6=1`), **not a joint pole at `Δ5+Δ6=2`.** This rules out, for this specific ordering,
the naive reading of the task's warning to "derive the shadow pole, don't assume it": a
bare energy-space Mellin transform of one color-ordered Feynman term is structurally the
wrong place to look, because legs 5 and 6 share no propagator in this ordering (that's
also exactly *why* sewing them supplies the missing box edge rather than duplicating an
existing one). The shadow-pair singularity `Δ5+Δ6=2` must instead come from the
`(z,z̄)`-plane OPE/conformal-partial-wave decomposition of the full correlator in the
56-exchange channel (the standard machinery `kinematic_block_v1.tex` already builds —
conical/Legendre reduction of the chiral block, the shadow-is-degree-symmetry theorem,
Mehler–Fock density) applied to this specific tree, not a property of one ordering's
energy integral — sharpening H1–H3 above by ruling out one candidate route to them.
**Not yet attempted:** the actual OPE-channel/conformal-partial-wave computation for
this tree. This finding is recorded, with the same classification, in Supabase
`research_notes` (kind `structural_no_go`) for cross-session continuity.

#### Follow-up, 2026-08-17 (same day, later): the OPE-channel/completeness-relation
computation, attempted from scratch — genuinely singular where the reconstruction
needs to happen, not a dead end

The honest boundary already on record for `ShadowPairSewing.sewing_identity` is
that its shadow-pair pole (`⟨O_Δ5 O_Δ6⟩ ∝ 1/(Δ5+Δ6-2)`) is a named hypothesis,
not something derived here from an actual two-point function or OPE computation.
This follow-up attempts that derivation genuinely, from
scratch, in `celestial_kinematics.py` + `shadow_sewing.py` (mpmath + sympy,
scratch-only, not committed — same convention as this thread's other companion
scripts). Method, with nothing inserted by hand at any step:

- Verified the standard celestial null-vector dot-product identity
  `q_i·q_j = +2(z_i-z_j)(z̄_i-z̄_j)` (mostly-minus metric) by direct symbolic
  expansion — not assumed from the literature, and caught a sign/factor-of-2 error
  in the first attempt before trusting it further.
- Built explicit, generic, asymmetric massless 4-momenta `p1,p2,p3,p4` for the
  6-point comb tree's fixed external legs (legs 1–4; only legs 5,6, the pair being
  sewn, are celestial/Mellin-transformed).
- **Step A**: Mellin-transformed leg 5 only: `L(Δ5,z5,z̄5) := ∫dω5 ω5^{Δ5-1}/(D1·D2)`.
  `D1,D2` are respectively a pure power and a linear function of `ω5`, so this is
  the classical Beta-function Mellin transform
  `∫w^{Δ-1}/(Bw+s)dw = πs^{Δ-1}/(B^Δ sin(πΔ))`. Verified this closed form against
  direct numerical quadrature at generic complex `Δ5` to machine precision
  (**after** catching and fixing a real bug: a finite quadrature cutoff at
  `w=2000` gave up to 8.7% spurious error from the integrand's slowly-decaying
  tail — using mpmath's genuine improper-integral limit fixed it to `~1e-11`–`1e-17`
  relative error; recorded as a lesson, not glossed over).
- **Step B**: Mellin-transformed leg 6 only: `R(Δ6,z6,z̄6) := ∫dω6 ω6^{Δ6-1}/D3`,
  `D3` a pure power of `ω6` — the Mellin transform of a bare power law, a genuine
  distribution (`Mellin[1](λ)=2πδ(λ)`), confirmed numerically by showing the
  regulated integral is bounded/oscillatory for `λ6≠0` but log-diverges as the
  cutoff is removed exactly at `λ6=0`.
- **Step C, the actual finding**: the physically correct sewing operation is the
  `SL(2,ℂ)` Plancherel completeness relation already used correctly in the
  existing `thm:shadow-disc` Step 5 (not a "search for a pole in `(Δ5,Δ6)`-space",
  which the prior finding above already ruled out): `Sewn = ∫dλ/2π P(λ) ∫d²z
  L(1+iλ,z) R(1-iλ,z)`. `R`'s delta-function support sits **exactly** at `λ=0`
  (forcing `Δ5=Δ6=1` on the shadow locus). Checked directly whether `L` is regular
  there: **it has a genuine simple pole at `Δ5=1`** (`|L(1+ε)|` grows as `1/ε` —
  confirmed numerically, `0.95, 9.6, 96, 962` for `ε=0.1,0.01,0.001,0.0001`, the
  correct `1/ε` scaling). **The naive real-`λ` completeness-relation sewing is
  therefore ill-defined as literally written for this tree ordering** — a
  zero-width delta function multiplying a simple pole is not a number.

**This is not a dead end — it is the first honest computational identification of
exactly where the missing analytic step must act.** A delta-function/pole collision
at precisely the point the reconstruction needs to be finite is the textbook
signature that the naive real-locus construction needs replacing by genuine
analytic continuation off that locus (deforming `Δ5,Δ6` into the complex plane,
extracting a residue/discontinuity there, then continuing back) — i.e. exactly the
Sokhotski–Plemelj/dispersion mechanism `DispersionReconstruction.lean` already
formalizes in the abstract, now with a concrete, verified target to apply it to.
**Not yet attempted**: the actual regularized extraction (deform off the real
locus, extract a finite residue/discontinuity, do the `z,z̄` integral, and check
whether what remains is recognizable as two-particle-cut/box data) — a substantial
further calculation, honestly scoped as the next step rather than rushed. No box
integrand has been reconstructed; none is claimed.

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

Beyond `sorry` (zero) and `axiom` (13 declarations), the tree carries **134
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
wall-count combinatorics; and most of the blackbody capstone's remaining structural theorems
(T1 triple equality, T3 logistic characteristic function, T6 Matsubara residues, T13
Fourier/Kirchhoff pair, T14) beyond the two (T2, T7-family) landed here. (T5, the cumulant
law, is now a plausible *next* target — see below.)

## Thread QG-Blackbody, round 2 — kinematic-block zeta bridge and the Weierstrass product for `sinh`

**Status: DONE, two new theorems, kernel-clean, no axiom, no sorry.** Continued straight
into `kinematic_block_v1.tex` after round 1, prioritizing what's actually reachable given
Mathlib's current special-function coverage (checked before attempting — see the gap list
below).

* **`QuantumGravity/KinematicZetaBridge.lean`** — `zeta_bridge_kappa`: Proposition
  `prop:zetabridge`(a) at the paper's own kernel normalization `κ(t) = (2sinh t)⁻¹`, giving
  `∫₀^∞ t^{s-1}κ(t)dt = (1-2^{-s})Γ(s)ζ(s)` directly (the leading factor of `2` in
  `SinhZetaBridge.sinh_mellin_zeta`'s conclusion exactly cancels `κ`'s own `1/2` — a
  five-line corollary once stated correctly).
* **`QuantumGravity/SinhWeierstrassProduct.lean`** — `tendsto_prod_one_add_sq_div`: the
  Weierstrass product `sinh(πλ) = πλ·∏ₙ(1+λ²/n²)`, proved as a genuine infinite product (a
  `Tendsto` statement for the partial products, for **every** real `λ`) — stronger than the
  capstone script's own certification (T4), which truncates at `N=2000` and bounds the tail
  by a Hurwitz-zeta remainder. Derived from Mathlib's `Complex.tendsto_euler_sin_prod`
  (Euler's product for `sin`, already in the pinned tree) via the substitution `z = iλ`:
  `sin(πiλ) = iλπ∏(1-(iλ)²/n²) = iλπ∏(1+λ²/n²)`, with `Complex.sin_mul_I` turning the left
  side into `i·sinh(πλ)`. The real-part extraction from the complex `Tendsto` needed three
  redone attempts before landing on fully-typed intermediate `have`s rather than chained
  in-place hypothesis mutations (`simp_rw ... at h`) — the untyped-mutation version keeps
  compiling but silently fails to collapse `Complex.re ∘ (single-cast sequence)` down to the
  plain real sequence, because a `simp_rw`/`rw` direction mismatch means the rewrite never
  fires and downstream errors point at the wrong step. Lesson for next time: when a chain of
  `have h := ...; simp only [...] at h; ... at h` steps produces a confusing "type mismatch
  after simplification" error far downstream, stop and give every intermediate `have` its
  full stated type — the error moves to exactly the step that's actually wrong instead of
  three steps later.

**What this unlocked**: `tendsto_prod_one_add_sq_div` was exactly the ingredient the
capstone's **T5 (cumulant law)** needed — `log P(λ) = -Σ(-1)^{k+1}ζ(2k)λ^{2k}/k`. See the
next round below: this is now DONE.

## Thread QG-Blackbody, round 3 — the cumulant law (T5)

**Status: DONE, `GppVerify/QuantumGravity/CumulantLaw.lean`, kernel-clean, no axiom, no
sorry.** `GppCumulantLaw.cumulant_law`: for `|λ| < 1`,
`-log(P(λ)) = Σ_{k≥0} (-1)^k·ζ(2(k+1))·λ^{2(k+1)}/(k+1)` (`k` zero-indexed, so `k+1` ranges
over the paper's `k≥1`) — exactly T5 of `verify_blackbody_capstone.py`
("cumulants are even zeta values"), `log P(λ) = -Σ_{k≥1}(-1)^{k+1}ζ(2k)λ^{2k}/k`.

Proof shape, following the plan above exactly:

* Take `log` of the Weierstrass product (`SinhWeierstrassProduct.tendsto_prod_one_add_sq_div`)
  via `Real.log_prod` on each finite partial product plus continuity of `log` at the positive
  limit `sinh(πλ)/(πλ)`, converting the `Tendsto` of partial products into
  `HasSum (fun j => log(1+λ²/(j+1)²)) (log(sinh(πλ)/(πλ)))` — summability of the log-series
  itself established via `log(1+x) ≤ x` compared against the shifted Basel series
  `Σ1/(j+1)²` (`summable_nat_add_iff` shifting Mathlib's `hasSum_zeta_two`).
* Expand each `log(1+λ²/(j+1)²)` via Mathlib's `hasSum_pow_div_log_of_abs_lt_one` (the
  standard `log(1-x)` Taylor series, applied at `x = -λ²/(j+1)²`), giving, for each `j`, a
  `HasSum` in the Taylor index `k`.
* Establish joint summability of the resulting `(j,k)`-indexed double array via an explicit
  product majorant `(1/(j+1)²)·(λ²)^{k+1}` (`Summable.mul_of_nonneg` on the two marginal
  geometric/Basel series), then upgrade from absolute to unconditional summability
  (`Summable.of_abs`).
* Swap the double sum (`Summable.tsum_comm`), and factor the inner `j`-sum's constants out
  via `tsum_mul_left` to land on the stated closed form.

Two genuine debugging lessons recorded for future double-series work in this repo:
(1) a `heartbeat` timeout appeared in the joint-summability lemma's calc chain and needed
`set_option maxHeartbeats 1000000 in` — a legitimate fix here (the chain is a real, if
slow, sequence of `positivity`/`div_le_div_of_nonneg_left` calls, not a genuine infinite
loop); (2) `rw [div_pow, ← pow_mul]` with no explicit arguments silently rewrote the wrong
one of two available `(a^m)^n` matches, leaving a residual `x^(2k)` vs `(x²)^k` mismatch that
`ring`/`ring_nf` cannot bridge on its own (they don't apply `pow_mul` for symbolic exponents)
— fixed by giving `pow_mul` its arguments explicitly (`← pow_mul lam 2 (k+1)`) to pin down
exactly which occurrence gets rewritten.

### Two genuine Mathlib gaps, scoped and named so a future session doesn't re-discover them

1. **No digamma/polygamma function at all.** `grep -rli "digamma\|polygamma"
   .lake/packages/mathlib/Mathlib/` returns **zero hits** at the pinned `v4.19.0` commit.
   Mathlib has `Complex.Gamma`/`Real.Gamma` and their differentiability
   (`Analysis/SpecialFunctions/Gamma/Deriv.lean`), but not `ψ = Γ'/Γ`, its Gauss/Weierstrass
   series `ψ(w) = -γ + Σ[1/(n+1) - 1/(n+w)]`, or the Euler–Mascheroni constant's defining
   properties needed to state `ψ(1/2) = -γ - 2log2`. This blocks **Theorem `thm:moment` (the
   First Moment Theorem)** of `kinematic_block_v1.tex` entirely — the paper's own six-step
   proof (partial fractions of `ψ`, a Laplace-transform identity for the resolvent, the
   `tanh²` Mehler–Fock-density collapse, a final geometric sum) is fully elementary and
   *would* port cleanly once `ψ` exists, but building the digamma function itself (from the
   Weierstrass product for `Γ`, or as a term-by-term derivative of the Gauss series) is its
   own multi-session foundational undertaking, not attempted here as a rushed partial version.
2. **No Legendre or conical special functions.** Confirmed by direct grep (repeated from
   round 1, still zero hits for `Legendre`/`conical`/`Mehler`). Blocks
   **Theorems `thm:conical` (2.1), `thm:shadowconn` (3.1), `thm:prefactor` (4.1),
   `thm:tempered` (4.4)** and the Mehler–Fock transform pair entirely — this is the paper's
   own largest and most novel piece (the conical reduction of the chiral kinematic block to
   a Legendre function of the second kind, and the shadow-transform symmetry as the Legendre
   degree involution `P_ν = P_{-ν-1}`), and building the needed special-function
   infrastructure from scratch is a separate, dedicated multi-session research arc — not
   something to bolt onto an existing thread.

Both gaps are now documented precisely enough (exact theorem names, exact missing Mathlib
objects) that a future session can pick either up directly instead of re-deriving the scope
from scratch.

---

## Thread QG-Blackbody, round 4 — Planck form and the reciprocal Weierstrass product

**Status: DONE, `GppVerify/QuantumGravity/SpectralWeightIdentities.lean`, kernel-clean, no
axiom, no sorry.** From updated companion papers ("The Spectral Weight π λ / sinh π λ" and
"Modular Thermality of the Celestial Spectral Weight"), with `verify_blocks_v2.py` and
`verify_ode_resolution.py` independently rerun (every claim reproduces to `1e-21`–`1e-41`
relative error) and `dispersion_step3a.py` — the loop-from-cut dispersion reconstruction —
independently verified for the first time this round (`0` to `1.6e-21` direct-vs-dispersion,
`1.4e-11`/`2.9e-7` for the Mellin-space dispersion relation).

* **`planck_form`**: for `λ > 0`, `P(λ) = 2πλ·(bose(πλ) - bose(2πλ))` where
  `bose(y) = 1/(exp y - 1)` — a genuine Planck-form identity for the spectral weight, proved
  by clearing denominators through `Real.sinh_eq` and the exponential of a sum.
* **`one_div_P_tendsto_tprod`**: `1/P(λ)` is the Weierstrass product `∏ₙ(1+λ²/n²)` as a
  `Tendsto` statement, an immediate corollary of `SinhWeierstrassProduct.
  tendsto_prod_one_add_sq_div` for `λ ≠ 0`.

Also corrected this round: `AllLoopFiniteness.lean` and the blueprint's QG-Blackbody chapter
described `P(λ)` as "the Plancherel spectral weight" and `𝓜_L` as a "Plancherel loop
measure" — both wrong (the `SL(2,ℂ)` Plancherel density for the scalar principal series
grows like `λ²`, not `P`). Retitled to describe `P` as what it is: the two-particle
massless phase-space weight of a celestial unitarity cut. No Lean statement or proof
changed — only doc comments and the blueprint's prose.

### Not yet formalized, scoped for a future round

* **The weight-shift ODE for `P`'s Fourier transform** (`P(λ∓i) = (1±iλ)/(∓iλ)·P(λ)`, and
  `(1/2)sinh(x)·p̂'(x) = p̂(x) - p̂(0)` for `p̂(x) = (1/4)sech²(x/2)`): pure real analysis, no
  digamma needed, but requires setting up the Fourier transform of `P` as an integral and
  differentiating under it — a real but bounded piece of work, not attempted this round.
* **The digamma-moment theorem** (`thm:moment`, First Moment Theorem) and the deviation
  moments `A_k` built on it: still blocked on digamma per round 3's gap #1 above — the new
  papers' closed-form proof of `thm:moment` is elementary once `ψ` exists, but `ψ` itself
  is not yet built.
* **Matsubara residues** (`Res_{λ=in} P(λ) = i(-1)^n n`): needs `P` continued to `ℂ` and
  Mathlib's residue-calculus machinery; not attempted this round.

---

## Digamma via Mathlib's `Gamma` calculus (task #9, closed)

**Status: DONE, `GppVerify/QuantumGravity/Digamma.lean`, kernel-clean, no axiom, no sorry.**
Earlier rounds' `grep` for the *name* `digamma`/`polygamma` in `.lake/packages/mathlib/`
(zero hits at pinned `v4.19.0`) was the wrong question — Mathlib's
`NumberTheory.Harmonic.GammaDeriv` already computes `deriv Real.Gamma` in closed form at `1`
(`Real.hasDerivAt_Gamma_one`, via the Bohr–Mollerup convexity argument) and at `1/2`
(`Real.hasDerivAt_Gamma_one_half`, via Legendre's duplication formula
`Real.Gamma_mul_Gamma_add_half`), and at every positive integer (`Real.hasDerivAt_Gamma_nat`).
`GppDigamma.digamma := deriv Gamma / Gamma` makes `ψ(1)=-γ`, `ψ(1/2)=-γ-2log2`,
`ψ(n+1)=-γ+harmonic n`, and the functional equation `ψ(x+1)=ψ(x)+1/x` immediate corollaries
— the last one needed `Filter.EventuallyEq.deriv_eq` on a neighborhood avoiding `x=0` rather
than a global `funext`, since `Gamma(s+1)=s·Gamma(s)` is literally false at `s=0` under
Mathlib's junk-value convention (`Gamma 1 = 1 ≠ 0 = 0·Gamma 0`) — the same care
`GammaDeriv.lean`'s own `hder_rec` takes for the analogous step.

**Real-argument only.** `kinematic_block_v1.tex`'s First Moment Theorem needs
`Re ψ(1/2+iλ/2)`, the *complex* digamma along a vertical line — a further, separate
extension, not attempted this round. Whether it is similarly close at hand (Mathlib's
`Complex.Gamma` differentiability is unconditional off the poles, but no closed-form complex
derivative values like `GammaDeriv.lean`'s exist yet) is worth a dedicated scoping pass next.

---

## New research front (2026-08-20): local-field shadow kernels

**Status: `GppVerify/QuantumGravity/{LocalShadowKernel,DiagonalConformalLift}.lean`, four +
four theorems, kernel-clean, no axiom, no sorry.** From Daniel's own "Local-field shadow
kernels, celestial unitarity, and the adelic principal series" — investigating whether
celestial Cutkosky unitarity, 1D Mellin/shadow harmonic analysis, and adelic PGL(2) harmonic
analysis share a common rank-one local-to-global structure. Full write-up, including the
genuinely open research problems (local factorization, Cutkosky-vs-Rankin-Selberg,
non-Archimedean-kernel-in-Lean gap), in
`discovery/local_field_shadow/local_shadow_kernel_notes.md` — do not duplicate that boundary
here; the summary is: shadow reflection and principal-series positivity for the Archimedean
kernel `K_{∞,d}(a)=Γ(a)Γ(d-a)/Γ(d)`, and the diagonal conformal lift `D(s)=(s,s)`,`Δ=2s`,
are proved unconditionally; the non-Archimedean kernel, the local factorization problem
(§9), the Rankin-Selberg bridge (§10), and the `ℝ₊`-as-principal-series-skeleton Lean
formalization (§4) are not — tracked as tasks #12–14.

---

## §9 resolution: the naive common-local-factor conjecture fails, informatively (2026-08-22)

**Status: DONE, `GppLocalShadow.{GammaC_eq_GammaR_mul_GammaR_succ,
archKernel_two_eq_GammaC_product, archKernel_two_eq_GammaR_sectors}` and
`GppEisenstein.{eisensteinCoeff_eq_shadow_ratio, eisensteinCoeff_reflection}`, five theorems,
kernel-clean, no axiom, no sorry.** Task #12's local factorization question — does a single
`a_∞(s)` give both the physical kernel and the Weyl intertwiner — answered **no** at the
level checked, and the failure is the informative structural fact: they are distinct
canonical objects on the same rank-one principal series. Full account, including the
Archimedean/finite-place/global breakdown and the honest remaining boundary (the *deeper*
representation-theoretic question of why, and whether some other factorization could still
relate them), in `discovery/local_field_shadow/local_shadow_kernel_notes.md`'s "§9
resolution" section — not duplicated here.

New Lean content:
* `GammaR`/`GammaC` (real/complex Archimedean Gamma factors) and `archWeylCoeff` (the
  spherical Weyl/Gindikin–Karpelevich coefficient, recorded for contrast only) added to
  `LocalShadowKernel.lean`.
* `GammaC_eq_GammaR_mul_GammaR_succ`: Legendre duplication `Γ_C(s)=Γ_R(s)Γ_R(s+1)`, derived
  from Mathlib's `Complex.Gamma_mul_Gamma_add_half`. The proof needed care around two
  `(2:ℂ)` vs `((2:ℝ):ℂ)` numeral-cast mismatches — `Complex.mul_cpow_ofReal_nonneg` only
  fires on bases syntactically cast from `ℝ`, so a small private helper
  (`two_mul_pi_cpow_split`) isolates the cast-and-split step once rather than fighting the
  mismatch inline at each use site.
* `archKernel_two_eq_GammaC_product` / `_GammaR_sectors`: the celestial `d=2` cut
  `K_{∞,2}(Δ) = π²Γ_C(Δ)Γ_C(2-Δ) = π²·Γ_R(Δ)Γ_R(Δ+1)·Γ_R(2-Δ)Γ_R(3-Δ)` — two shadow-paired
  real Archimedean Gamma sectors.
* New file `GlobalEisensteinCoefficient.lean`: `eisensteinCoeff Δ := Λ(Δ-1)/Λ(Δ)` (`Λ` =
  Mathlib's `completedRiemannZeta`) rewrites exactly as `Λ(2-Δ)/Λ(Δ)` and satisfies
  `φ(2-Δ)φ(Δ)=1`, both immediate from Mathlib's own `completedRiemannZeta_one_sub`
  functional equation (`Λ(1-w)=Λ(w)` for every `w`, unconditional — a genuinely useful piece
  of pre-existing Mathlib infrastructure found by checking before assuming it was missing,
  the same lesson as the digamma find two rounds ago). **Not an RH claim** — Eisenstein
  scattering containing `ζ(s)` in its functional equation proves nothing about its zeros;
  `|φ(1+iλ)|=1` is verified numerically only, since it needs `Λ`'s conjugation symmetry,
  which Mathlib does not state directly for `completedRiemannZeta`.

Also independently verified numerically (not Lean claims): `c_∞`/`archKernel` are not
proportional at the Archimedean place; the Gindikin–Karpelevich coefficient and the derived
finite-place kernel are not equal. Task #12 marked resolved at this level; a follow-up task
for the deeper representation-theoretic question would need to be scoped fresh if pursued.

---

## The golden ratio as the minimal hyperbolic sector of `PSL₂(ℤ)` (2026-08-22)

**Status: DONE, `GppVerify/NumberTheory/GoldenRatioHyperbolicSector.lean`, fourteen
theorems, kernel-clean, no axiom, no sorry.** From a research-front update: `F = T∘J`
(unit translation after inversion), `F(x)=1+1/x`, has unique positive fixed point `φ`.
Projectively, `M=!![1,1;1,0]`, `A:=M²=!![2,1;1,1]` is the minimal-trace hyperbolic element
of `SL₂(ℤ)` — integrality forces `|tr|≥3` once `|tr|>2` (hyperbolicity), and `A` attains it.
Discriminant `5`, eigenvalues (as characteristic-polynomial roots) `φ^{±2}`, Möbius fixed
points `φ` and `-φ⁻¹`. Independently, the finite-place shadow kernel `K_{q,1}(s)`
(`discovery/local_field_shadow/`, §5 — used here only via its closed-form real-function
definition, not the underlying `p`-adic integral) evaluated at `q=5` (the *independently*
selected discriminant — `φ` never enters the kernel's definition or the choice of `q`) and
`s=1/2` equals exactly `φ²`. `golden_convergence` connects the two routes.

Reuses Mathlib's `Data.Real.GoldenRatio` throughout (`goldenRatio`, `gold_sq`,
`gold_ne_zero`, `goldConj_neg`, `gold_add_goldConj`, `gold_mul_goldConj`, `inv_gold`,
`one_lt_gold`) rather than redefining any of it. Matrix identities use plain
`Matrix (Fin 2) (Fin 2) ℤ` with `Matrix.det_fin_two_of`/`trace_fin_two_of`/`mul_fin_two`,
not Mathlib's `SpecialLinearGroup`/`ModularGroup` machinery (that machinery targets the
action on the upper half-plane `ℍ`; this package needs the real-line Möbius fixed points
and elementary `2×2` determinant/trace facts instead, which are simpler used directly).

**Missing-interface note, precisely as requested**: the "characteristic polynomial" facts
(`A_charpoly_root_goldSq`/`_goldInvSq`) are stated as direct roots of `X²-(tr A)X+(det A)`,
not connected to Mathlib's `Matrix.charpoly`/`Module.End.HasEigenvalue` API — no
`charpoly_fin_two`-style closed form for `2×2` matrices was found in the pinned Mathlib
(`v4.19.0`); building that bridge is real, separate work, not attempted.

**Semantic boundary, deliberately not formalized**: that this "minimal modular hyperbolic
sector" is the *physical* fundamental sector of anything in the surrounding research
program — open and physical, not mathematical, no theorem asserts it. Nor that inversion
*alone* forces `φ` — the actual claim needs primitive translation too.

Independent numerical cross-check: `discovery/local_field_shadow/golden_hyperbolic_verify.py`
(supplementary to the Lean proofs, not a substitute).

## Thread Cutkosky-Weil — local shadow kernels and the finite-prime Weil kernel (2026-08-22/23)

**Status (fifth pass): local identities, the layered finite Fourier/Gram-square
development, the removable singularity, the full `N→∞` analytic passage, AND the
operator-level vacuum-compression identity all DONE,
`GppVerify/RiemannHypothesis/CutkoskyWeilBridge.lean` — 24 theorems, all kernel-clean, no
axiom, no sorry, culminating in the genuine, untruncated
`GppHaarPositivityWeil.PositiveType (K_r - 1)` (`KrClosed_minus_one_positiveType`) AND the
actual bounded-operator identity `C_{K_r-1} = P_0 * C_{K_r} * P_0` on `ℓ²(ℤ,ℂ)`
(`vacuum_compression_operator_identity`) with its positivity corollary
(`vacuum_compressed_operator_positive`), both unconditional. The Mellin/adelic bridge to
the classical Weil kernel, `Q_GPP`, and global positivity factorization are NOT
attempted — see the fifth-pass paragraphs below for the precise, re-scoped target.**

From a research-front directive proposing the route `celestial Cutkosky positivity →
local shadow kernels → finite-prime Weil kernel → Casimir compression → global Weil
positivity → RH`, with the explicit instruction not to import Connes–Consani's
scaling-trace machinery and to attack the "missing analytic bridge" instead. The final
logical step (finite Weil paired-form positivity on all nontrivial zeros ⟺ RH) is
already proved unconditionally in `WeilPositivityCriterion.lean`
(`rh_iff_weil_pairedForm_nonneg`) — but that criterion is an *abstract* pairing over
finite subsets of the actual (unknown) zero set, not the classical Weil explicit-formula
prime-sum quadratic form the directive describes; bridging the two needs the classical
explicit formula itself (a separate, substantial, not-in-Mathlib undertaking), named
here as an honest boundary rather than forced.

**What's proved**: `Kp p t` (the finite-place shadow kernel, real closed form
`(1-p⁻¹)/(1-2p^{-1/2}cos(t log p)+p⁻¹)`) is positive for every `p>1` (`Kp_pos`) — a
one-line consequence of it being a Poisson-kernel value. `H t := (t²+1/4)·cutKernel t`
(the Casimir-weighted Archimedean kernel, `cutKernel` the already-derived celestial cut
`t/(4 sinh(2πt))`) is nonnegative for every real `t` (`H_nonneg`) — `t` and
`sinh(2πt)` always share sign.

**Self-correction, then the corrected central finding.** A first round's numerical
"central finding" claimed no positivity-preserving projection from `K_p` to `K_p−1`
exists — that claim was **wrong**, caught by review after it had already merged to
`main`. It tested a Toeplitz matrix of Fourier *coefficients* (indices = frequencies),
not the actual kernel-positivity Gram matrix (indices = point evaluations); those are
different objects. **Corrected finding: `K_p − 1` IS a positive kernel, prime-by-prime,
unconditionally** — convolution by `K_p` is diagonal in the Fourier basis with
eigenvalues `r^{|n|}≥0`; the vacuum subtraction merely zeroes the `n=0` eigenvalue,
which cannot make the rest negative. This is now proved rigorously in Lean at every
finite truncation via a **layered finite Fourier/Gram-square development**:
`gram_square_freq` (fixed-frequency Gram identity, generalizing
`ConvolutionSquarePositive.lean`'s `gram_square_nonneg` to complex amplitudes) →
`gram_square_freqSum` (finite weighted sum over frequencies) →
`gram_square_freqSum_nonneg` (nonnegativity corollary) → `KrN0`/`KrN0_gram_nonneg` (the
truncated kernel `K⁰_{r,N}=Σ_{0<|n|≤N}r^{|n|}e^{inθ}` and the milestone theorem
`Σᵢⱼc̄ᵢcⱼK⁰_{r,N}(xᵢ-xⱼ)≥0`). Each layer builds independently in under 4 seconds.

**Proof-engineering lesson (worth repeating for future threads)**: a first attempt at
the corrected result proved the untruncated two-sided `HasSum` over all of `ℤ` and built
`PositiveType(K_r-1)` on top of it as one monolithic theorem — both repeatedly hit
`(deterministic) timeout at whnf` even at 4,000,000 heartbeats (20× default). Bisected by
extracting sub-`have`s into standalone scratch files tested with `lake env lean` at
*default* heartbeats (seconds, not minutes, per test) rather than waiting out repeated
multi-minute full-file builds. Root causes: (1) `HasSum.of_nat_of_neg_add_one` elaborates
in under 20s with a minimal local context but times out inlined into a context also
carrying `r, hr0, hr1, θ` — extracted as its own minimal-context lemma; (2) the full
Gram-square argument, run once over an infinite series with `ring_nf`/`nlinarith` on
deeply nested `Complex.re`/`Complex.im` terms, accumulates unbounded elaboration cost
regardless of heartbeat budget. Fixed architecturally (the four small layers above), not
by raising `maxHeartbeats` further. **If a theorem takes more than ~1 minute to
elaborate, treat that as a proof-engineering bug and bisect — don't just raise the
heartbeat limit.**

This does **not** rule out — nor does it establish — global positivity of the assembled
sum `Q_GPP = Q_∞ + Σ_p Q_p`; single-prime kernel positivity was never going to answer
that on its own (the classical Weil explicit formula's local prime terms are
individually sign-indefinite in their usual normalization even though local `K_p`
positivity holds).

**Fourth pass (same session, following review) — both items above landed.** (1) The
removable singularity: `tendsto_cutKernel_zero` proves `cutKernel → 1/(8π)` as `t→0`
(`t≠0`), from `Real.sinh`'s derivative at `0` (`HasDerivAt Real.sinh (Real.cosh 0) 0`),
not asserted; `cutKernelExt := Function.update cutKernel 0 (1/(8π))` is the continuous
extension (`continuousAt_update_same` turns the punctured-neighborhood limit directly
into continuity); `Hext`/`Hext_zero`/`Hext_nonneg` give `H(0)=1/(32π)` and nonnegativity
everywhere, replacing the earlier `0/0=0` junk value. (2) The `N→∞` passage, via the
route review specified — separate convergence from algebra rather than reviving the
timed-out monolithic construction: `tendsto_Icc_atTop` (symmetric intervals are cofinal
in `Finset.atTop`) + `summable_KrClosed_summand` (`Summable`, existence only, via
`Summable.of_nat_of_neg` compared against the geometric tail — far cheaper than tracking
`HasSum` *values* through `Int.rec`) + `tsum_KrClosed_summand_eq` (the tsum's value
identified as `K_r(θ)-1`, via the two one-sided geometric series and
`Summable.tsum_of_nat_of_neg`) + `tendsto_KrN0` (`KrN0 → K_r(θ)-1`) +
`KrClosed_minus_one_positiveType` (positivity passes to the limit via `ge_of_tendsto`) =
the genuine, untruncated `GppHaarPositivityWeil.PositiveType (K_r - 1)`, unconditional.
16 theorems total in the file now, all kernel-clean.

**Still deferred, not attempted**: the exact Fourier pair
`H(t) ↔ G(x)=3/(512π)sech⁴(x/4)` under the convention `G(x)=(1/2π)∫H(t)e^{itx}dt`
(confirmed numerically to ~1e-51 relative error; needs Mathlib Fourier-transform-of-sech⁴
machinery not confirmed to exist); the pole-cancellation/removable-singularity claim at
`t=±i/2` (a different, complex-analytic singularity from the real-axis one at `t=0` just
closed — confirmed numerically via a shrinking-perturbation sequence, no formal residue
calculus).

**Fifth pass (same session, following a further review directive) — the operator identity
closed; the finite-prime Weil-kernel target precisely re-identified.** The directive named
a six-item program prioritizing item 1 (the actual operator statement, not the finite
Fourier identity again) and item 4 (the Mellin/adelic bridge). Item 1 is now DONE in full:
`Ell2Z := ℓ²(ℤ,ℂ)`, the natural Fourier-coefficient model (Parseval-dual to the circle, so
convolution-by-kernel becomes diagonal multiplication by Fourier coefficients — no need to
build the circle convolution operator itself). `mulOpCLM w hw : Ell2Z →L[ℂ] Ell2Z` is the
bounded diagonal `ContinuousLinearMap` for any weight bounded by `1` (built via
`LinearMap.mkContinuous` from an explicit norm bound). `C_{K_r} := mulOpCLM(KrWeight r)`,
`P_0 := mulOpCLM P0Weight` (the vacuum-deleting projection), `C_{K_r-1} :=
mulOpCLM(KrMinusOneWeight r)`. **`vacuum_compression_operator_identity`**:
`C_{K_r-1} = P_0 * C_{K_r} * P_0` as genuine `ContinuousLinearMap` composition, via
composition-multiplies-symbols (`mulOpLin_comp`) reducing to the one-line pointwise fact
`P_0(n)·K_r(n)·P_0(n)=(K_r-1)(n)`. **`vacuum_compressed_operator_positive`**: positivity of
the compressed operator, derived as a genuine corollary of a *general* lemma
(`mulOpCLM_inner_re_nonneg`: any bounded diagonal operator with `Re(w(n))≥0` everywhere is
positive semidefinite) applied to `K_r-1`'s already-known eigenvalue signs — no new
analytic content, exactly "as a corollary" as directed. 8 new theorems, kernel-clean, no
axiom, no sorry.

Checking `GppWeilCriterion.rh_iff_weil_pairedForm_nonneg`'s actual statement against the
directive's framing ("in the normalization used by" that theorem) found this file's own
prior module doc had already flagged the mismatch: `pairedForm` is a **zero-indexed**
reflection pairing over the (unknown) zero set itself, paired by `ι(ρ)=1-ρ̄` — it carries
no prime, Mellin, or Haar-measure content whatsoever for a "finite-prime Weil kernel in
this normalization" to mean. The genuine classical target is
`GppHaarPositivityWeil.weil_criterion` (`D_k=Σ_ρΩ̂(ρ)+local terms`), a full `True`-stub
honestly blocked on Tate's thesis + idèle class groups — neither in Mathlib, a large,
well-known, multi-year gap, not proof-engineering-fixable. But the classical *elementary*
(non-adelic) explicit formula's finite-prime local term has a clean checked closed form:
with `ζ_p(s):=(1-p^{-s})^{-1}` the local Euler factor, `Wp(p,t) =
2·Re(-ζ_p'/ζ_p(1/2+it))` exactly — derived by hand from `-ζ_p'/ζ_p(s)=log(p)Σ_{k≥1}p^{-ks}`
(standard log-derivative of the Euler factor) plus the already-proved
`Kp_eq_KrClosed`/`tsum_KrClosed_summand_eq`. Checked, not yet Lean-formalized — the honest
next Lean target for items 2–3, no new Mathlib gap. Item 6 (global assembly against
`rh_iff_weil_pairedForm_nonneg`) does not apply as stated, for the same reason: that
theorem's hypothesis carries no prime-side data to assemble. The genuine assembly question
belongs to `weil_criterion`, and even granting the `Wp` identity for its local terms, still
needs the *global* explicit formula (contour integration of `ζ'/ζ`, the argument
principle) to exist in Lean first — not currently in the tree, a separate substantial
classical-analytic-number-theory undertaking (smaller than the adelic route, still large),
scoped honestly, not attempted. Full account: `discovery/cutkosky_weil/notes.md`, "Fifth
pass" section.

**Item 3 (Casimir operator's representation-theoretic origin) — not attempted**: the
precise missing interface is Mathlib's total absence of `SL(2,ℝ)` principal-series
representations or a Casimir/Laplace–Beltrami operator; `t²+1/4` is used here purely as
the known eigenvalue *number*, not derived from an actual operator. Building that
operator is separate, substantial representation-theory work.

**Item 9 — no Connes–Consani/Selberg/Mayer/Tate/Knapp–Stein machinery imported**
anywhere in this thread; the Gram-square development is original to this session,
derived purely from the GPP local-shadow-kernel route already in the tree.

**Explicit non-claims**: no RH claim and no claim of global Weil positivity. Local
positive-type positivity of `K_p−1` *is* proved; it does not transfer automatically to the
standard explicit formula, whose finite-prime contribution carries the opposite overall
sign and uses a different test-function pairing.  The sign of that pairing is not fixed by
the overall minus sign alone. No external RH program's machinery is imported as a black
box.

## Thread Cutkosky-Weil, sixth pass (2026-08-23) — the Euler-factor identity and the
## decisive sign question

Attacking the bridge from the already-proved `Wp`/`Kp-1` local kernel positivity
(`CutkoskyWeilBridge.lean`, fifth pass) to the classical Weil explicit formula's
finite-prime term, per a relayed research directive, rather than continuing to circle
the abstract `rh_iff_weil_pairedForm_nonneg` criterion.

**Layer 1-2 landed in Lean** (`GppVerify/RiemannHypothesis/EulerFactorLogDeriv.lean`,
new file, imported into `GppVerify.lean`): `zetaP p s := (1-exp(-s log p))⁻¹`, the local
Euler factor as a genuine function of `s : ℂ`. `hasDerivAt_zetaP` proves the closed form
`minusLogDerivZetaP p s := log(p)·p^{-s}/(1-p^{-s})` genuinely **is** `-ζ_p'(s)/ζ_p(s)`,
from an actual `HasDerivAt` chain-rule computation (through `Complex.exp`, then
`HasDerivAt.inv`) — not asserted from the geometric-series shortcut. Full project
rebuild green: 3300/3301, sorry-gate clean, 13/13 axioms unchanged.

**Honest boundary, this pass**: the final connection back to `Wp` — `Wp p t =
2·Re(minusLogDerivZetaP p (1/2+it))` — is checked by hand and numerically to 40 digits
(four primes × three `t` values, `verify_euler_factor_logderiv.py`) but not yet
formalized: the `Complex.cpow` exponent-splitting algebra
(`p^{-(1/2+it)}=p^{-1/2}·p^{-it}`) needs more care than this pass affords without
iterative compiler feedback on this large a file. Named precisely, not forced through.

**The decisive question, answered by direct computation, not assumption.** Does the
already-proved positive-type property of `Wp`'s kernel help establish the sign the Weil
explicit formula's prime term actually needs? Rather than trust a half-remembered
normalization, verified Weil's explicit formula itself against 60 real nontrivial zeta
zeros (`mpmath.zetazero`) with a concrete even Gaussian test function
`h(r)=exp(-0.6 r²)`:
```
sum_rho h(gamma) = h(i/2)+h(-i/2) - g(0)log(pi) + (1/2pi) int h(r) Re[psi(1/4+ir/2)] dr
                    - 2 sum_{n>=2} (Lambda(n)/sqrt(n)) g(log n)
```
Both sides agree to `~1e-10`, pinning the sign exactly: the prime sum enters with an
overall **minus** sign. Its summand is exactly `-2·sum_p sum_m log(p)·p^{-m/2}·g(m log p)`
— literally minus a quantity built from the same Poisson-kernel structure `Wp` already
proved positive-type (`verify_weil_explicit_formula_sign.py`).

**Finding, later corrected in the eighth pass below:** the Gaussian calculation proves a
negative prime contribution for that test and pins the overall sign, but this pass first
inferred universal nonpositivity.  That was too strong: positive-type **convolution** by
`Kp-1` is not the same operator as **multiplication** by `-Wp` after the test-function
transform.  The eighth pass proves that the scalar multiplier changes sign.  The numerical
identity and Gaussian result remain valid; the universal-sign inference is withdrawn.

**A new asset**: Daniel supplied 100,000 high-precision nontrivial zeta zeros (Odlyzko
format); the missing first zero was prepended by hand
(`γ₁=14.134725141734693790457251983562470270784257115699...`). Ran `zeta_screw.py`'s
Stage 3 ("Gram identity from the zeros") with this real file for the first time, ranges
`±1,±2,±3`: relative residual `13-16%`, not the "small residual" clean-confirmation case
the script's own docstring anticipates — recorded honestly as a real, moderate-but-not-
tiny result, not yet diagnosed further (more zeros/higher truncation cutoff untested), a
loose end for a future pass, not claimed as confirmation or refutation either way.

Full detail: `discovery/cutkosky_weil/notes.md` (sixth-pass section),
`verify_euler_factor_logderiv.py`, `verify_weil_explicit_formula_sign.py`.

## Thread Cutkosky-Weil, seventh pass (2026-08-23) — the `Wp` boundary, closed

Closes the honest boundary named above: `Wp p t = 2·Re(minusLogDerivZetaP p (1/2+it))` is
now a genuine Lean theorem (`Wp_eq_two_mul_re_minusLogDerivZetaP`,
`EulerFactorLogDeriv.lean`), not just checked by hand and numerically. Proved by direct
real/imaginary-part computation (`Complex.exp_re`/`exp_im`, `Complex.div_re`,
`Complex.normSq_apply`) rather than the originally-attempted `Complex.cpow`
exponent-splitting route, closing with a standalone Poisson-kernel lemma
`KrClosed_sub_one_eq_two_mul_re`: for real `r, θ` with `0 ≤ r < 1`,
`KrClosed r θ - 1 = 2·Re[r·e^{iθ}/(1-r·e^{iθ})]`.

**A genuine correction made mid-proof, not glossed over**: the first draft of
`KrClosed_sub_one_eq_two_mul_re` was stated for *all* real `r, θ`, unconditionally — this
is actually **false**. At `r=1, θ=0` the denominator `1-r·e^{iθ}` vanishes; Lean's total
division sends `KrClosed 1 0 - 1` to `-1` (since `(1-1²)/0 = 0/0 = 0` by convention) but the
right-hand side to `0` (since `1/0=0` there too, but the algebra path differs), so the
"theorem" as originally stated would have been unprovable — caught by working the r=1,θ=0
case by hand before trying to push the proof through `nlinarith`, not by the compiler
rejecting a false universal claim (Lean has no way to know a stated theorem is false until
you fail to prove it). Fixed by adding `0 ≤ r < 1` hypotheses, which cost nothing since the
only application is `r = p^{-1/2} < 1` for `p > 1`.

Full project rebuild: 3300/3301 clean, sorry-gate clean, 13/13 axioms unchanged. Committed
`4bc283e` on `cutkosky-weil-euler-factor`, branched from `origin/main`.

**Explicit non-claim**: this does not touch the decisive-question finding (sixth pass) —
the sign obstruction concerns how `Wp` enters the classical explicit formula, which this
pass does not address; it only proves what `Wp` genuinely *equals*.

**Next honest boundary**: the exact test-function-transform theorem and the classical
explicit formula itself (contour integration of `ζ'/ζ`, the argument principle) remain
unformalized, as does the global prime--Archimedean/no-ghost projection.

## Thread Cutkosky-Weil, eighth pass (2026-08-23) — prime powers and the exact local
## sign obstruction

`EulerFactorLogDeriv.lean` now contains the complete two-sided prime-power expansion.
`primePowerCoeff p n = log(p)p^{-|n|/2}`, `primePowerFrequency p n=n log p`, and
`WpFourierTerm` omits the vacuum mode. `summable_WpFourierTerm` proves absolute
summability and `tsum_WpFourierTerm_eq` proves
`Wp(p,t)=Σ_{n≠0}log(p)p^{-|n|/2}exp(i n t log p)` exactly.

The decisive correction is also formalized. `Wp_zero_pos` proves `Wp(p,0)>0`, while
`Wp_antiphase_neg` proves `Wp(p,π/log p)<0`. With the named signed scalar term
`weilPrimeMultiplier := -Wp`, `weilPrimeMultiplier_sign_changes` proves that it takes
both signs for every real `p>1`. Therefore:

- the convolution operator from `Kp-1` remains positive because its Fourier eigenvalues
  are nonnegative;
- the scalar explicit-formula multiplier is sign-indefinite;
- the sixth-pass Gaussian result sampled one sign and cannot establish universal
  nonpositivity for every Weil square.

The latest arithmetic manuscript supplies a substantive fermionic/spinorial candidate for
the missing global mechanism: a finite exterior-algebra prime space with CAR creation and
contraction operators, a Koszul differential `d_z²=0`, and a positive Hodge--Dirac square
`(d_z+d_z†)²≥0`. The scalar `Wp` is therefore plausibly a local supertrace/shadow of that
graded complex, not itself a spinor field. The global positivity target is a completed
physical-sector/no-ghost theorem (even-degree Hodge/OS cohomology), analogous to selecting
one time orientation; it remains unproved and must not be assumed.

## Thread Cutkosky-Weil, ninth pass (2026-08-23) — exact boundary propagation and local
## fermionic Dirac structure

Two new Lean modules close the next physics-to-arithmetic interfaces.

**`RiemannHypothesis/PrimeGreenAmplitude.lean`.** The `Wp` positive-frequency coefficient
and frequency are proved identical to the arithmetic boundary weight
`log(p)p^{-m/2}` and location `m log p`.  For every finite family,
`finitePrimeGreenAmplitude_eq` proves the exact massive Green identity

`Σ log(p)p^{-m/2} exp(-r m log p)/(2r)
 = (1/(2r))Σ log(p)p^{-m(1/2+r)}`.

Both finite amplitudes are nonnegative for `r>0`.  The abstract doubled-sector
polarization identity `⟪a,b⟫=(‖a+b‖²-‖a-b‖²)/4` is also proved, justifying the even/odd
boundary cross-term mechanism without constructing or assuming the completed boundary.

**`RiemannHypothesis/PrimeFermionDirac.lean`.** The exterior algebra on one prime generator
is implemented as a two-state matrix system. Creation/contraction satisfy CAR; the local
supercharge squares to zero; the Hodge--Dirac operator is self-adjoint, anticommutes with
fermion parity, and obeys `D(z)²=normSq(z)I`.  With the exact Euler holonomy
`z=1-exp(-s log p)`, its inverse is `zetaP`.  `eulerHolonomy_critical_ne_zero` and
`primeDiracEnergy_critical_pos` prove that every isolated local prime system has strictly
positive energy on the critical line.  Therefore the local spinorial description is now
a theorem, while physical zeros remain necessarily collective/global.

**Twin-prime correlation layer.** `NumberTheory/TwinPrimeDoublets.lean` proves that if
`p-2,p,p+2` are prime then `p=5`; above `5`, every prime is exactly a gap-2 singlet or a
member of one one-sided doublet. `3-5-7` is the unique overlapping triplet.  This is a
rigorous two-prime graph decomposition, not a proof of twin-prime infinitude and not an
asserted `SU(2)` representation.  Conjecturally the doublet sector is infinite but
density-zero among primes.

**`RiemannHypothesis/PrimeDoubletDirac.lean`.** The graph decomposition now has exact
operator blocks.  The isolated block is zero.  The twin block is the exchange matrix
`[[0,1],[1,0]]`, proved equal to the unit-holonomy rank-one Hodge--Dirac operator `D(1)`.
Lean proves its `+1` symmetric state, `-1` antisymmetric state, failure of positive
semidefiniteness, identity square, and positive-semidefinite squared block.  Thus the
doublet clue supports a first-order Dirac/sign-pairing structure; positivity can occur at
the squared/Hodge level, not for the raw twin adjacency.

**Next:** finite multi-prime Koszul/CAR infrastructure with the actual commuting Euler
holonomies, followed by the completed Archimedean boundary/no-ghost obstruction.  The
twin-edge graph is a candidate interaction layer inside that construction; it must earn
any physical representation-theoretic interpretation through an explicit operator.

---

*History: earlier arcs (p-adic Tate thread PRs #44–58, Cesàro/Abel/Yakaboylu elementary
layer PRs #59–64) predate this document; see git log. Thread completions are recorded
here as they merge.*
