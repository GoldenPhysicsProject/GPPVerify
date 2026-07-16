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

**Status: in progress — `QuantumGravity/SinhZetaBridge.lean`, lands with the PR updating
this line.** From `kinematic_block_v11.tex` (Prop. zetabridge, "verified to 29 digits")
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

**Status: in progress — `RiemannHypothesis/WeilSupportLadder.lean`, lands with the PR
updating this line.** From arXiv:2106.01715 §2.2 via the joint-session prompt. Contents:
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

**Status: running — `scratchpad/weil_nearnull.py`, mpmath dps 45.** Protocol per the
joint-session prompt: basis `(1−(y/a)²)³·P_n(y/a)` (C² edges → `|ĝ|² ~ t⁻⁸`, zero-side
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

*Standing honesty note: nobody is proving RH itself here, and this plan does not pretend
otherwise. The value is that every reduction and every constant in the surrounding tower
is kernel-checked, with each remaining gap precisely named.*

---

*History: earlier arcs (p-adic Tate thread PRs #44–58, Cesàro/Abel/Yakaboylu elementary
layer PRs #59–64) predate this document; see git log. Thread completions are recorded
here as they merge.*
