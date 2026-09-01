-- ============================================================
-- The Riemann Hypothesis via Spectral Multiplicity
-- Author: Daniel Toupin | Golden Physics Project
-- ORCID: 0009-0003-7682-9579 | goldenphysics.org
-- Lean 4 / Mathlib v4.33.1
-- ============================================================
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Analysis.Distribution.SchwartzSpace
import GppVerify.RiemannHypothesis.ExpNotTempered
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

open Complex MeasureTheory Set HurwitzZeta
open scoped Real ComplexConjugate

namespace GppRH

/-- Companion imaginary part: Im(1 - conj rho) = Im(rho). -/
lemma companion_im_eq (rho : Complex) :
    (1 - starRingEnd Complex rho).im = rho.im := by
  simp [Complex.sub_im, Complex.one_im, RCLike.star_def, Complex.conj_im]

/-- When Re(rho) != 1/2, the companion 1 - conj(rho) is distinct from rho. -/
lemma companion_ne_of_off_critical (rho : Complex) (h : rho.re ≠ 1 / 2) :
    (1 - starRingEnd Complex rho) ≠ rho := by
  intro heq
  apply h
  have hre : (1 - starRingEnd Complex rho).re = rho.re :=
    congr_arg Complex.re heq
  simp [Complex.sub_re, Complex.one_re, RCLike.star_def, Complex.conj_re] at hre
  linarith

/-- Functional equation: zeta(rho) = 0 implies zeta(1 - rho) = 0. -/
lemma zeta_zero_implies_fe_zero (rho : Complex)
    (hzero : riemannZeta rho = 0)
    (hn : forall n : Nat, rho ≠ -↑n)
    (hone : rho ≠ 1) :
    riemannZeta (1 - rho) = 0 := by
  rw [riemannZeta_one_sub hn hone, hzero, mul_zero]

-- Supporting lemmas for riemannZeta_conj (proved below)

private lemma mellin_conj_of_im_zero {f : ℝ → ℂ} (hf : ∀ t, (f t).im = 0) (s : ℂ) :
    mellin f (conj s) = conj (mellin f s) := by
  simp only [mellin]
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [map_smul, smul_eq_mul, map_mul]
  congr 1
  · rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt ht)),
        cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt ht)),
        ← exp_conj, map_mul, ← ofReal_log (le_of_lt ht), conj_ofReal, map_sub, map_one]
  · exact Complex.ext (by simp [conj_re]) (by simp [conj_im, hf t])

private lemma hurwitzEvenFEPair_zero_fmodif_im (t : ℝ) :
    ((hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t).im = 0 := by
  simp only [WeakFEPair.f_modif, hurwitzEvenFEPair, smul_eq_mul, mul_one, Function.comp]
  simp only [Pi.add_apply, Set.indicator_apply, Set.mem_Ioi, Set.mem_Ioo]
  split_ifs <;>
    simp [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.one_im, Complex.zero_im]

private lemma conj_two_eq : conj (2 : ℂ) = 2 := by
  have h : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
  rw [h, conj_ofReal]

private lemma completedHurwitzZetaEven₀_zero_conj (s : ℂ) :
    completedHurwitzZetaEven₀ 0 (conj s) = conj (completedHurwitzZetaEven₀ 0 s) := by
  simp only [completedHurwitzZetaEven₀, WeakFEPair.Λ₀]
  rw [show conj s / 2 = conj (s / 2) by rw [map_div₀, conj_two_eq]]
  rw [mellin_conj_of_im_zero hurwitzEvenFEPair_zero_fmodif_im]
  rw [map_div₀, conj_two_eq]

private lemma completedHurwitzZetaEven_zero_conj (s : ℂ) :
    completedHurwitzZetaEven 0 (conj s) = conj (completedHurwitzZetaEven 0 s) := by
  simp only [completedHurwitzZetaEven_eq, show (0 : UnitAddCircle) = 0 from rfl, if_true]
  rw [completedHurwitzZetaEven₀_zero_conj]
  simp [map_sub, map_div₀, map_one, conj_two_eq]

private lemma Gammaℝ_conj_eq (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  simp only [Gammaℝ]
  have harg : (↑Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)]
    exact Real.pi_pos.ne
  have hcd : conj s / 2 = conj (s / 2) := by rw [map_div₀, conj_two_eq]
  have hne : -(conj s) / 2 = conj (-(s / 2)) := by
    rw [map_neg, map_div₀, conj_two_eq, neg_div]
  simp only [hne, hcd, map_mul, ← Complex.Gamma_conj]
  congr 1
  rw [cpow_conj (↑Real.pi : ℂ) (-(s / 2)) harg, conj_ofReal]
  congr 1; ring

private lemma hurwitzZetaEven_zero_conj (s : ℂ) :
    hurwitzZetaEven 0 (conj s) = conj (hurwitzZetaEven 0 s) := by
  by_cases hs : s = 0
  · subst hs
    simp [hurwitzZetaEven_apply_zero, conj_two_eq]
  · have hcs : conj s ≠ 0 := by simp [hs]
    rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inr hcs),
        hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs),
        map_div₀, ← completedHurwitzZetaEven_zero_conj, ← Gammaℝ_conj_eq]

/-- Reality: zeta(conj s) = conj(zeta(s)).
    Follows from: riemannZeta = hurwitzZetaEven 0, the Mellin transform of a real-valued
    kernel has conjugate symmetry, and the Gamma factor satisfies Gamma(conj s) = conj(Gamma s). -/
theorem riemannZeta_conj (s : Complex) :
    riemannZeta (starRingEnd Complex s) = starRingEnd Complex (riemannZeta s) := by
  simp only [riemannZeta]
  exact hurwitzZetaEven_zero_conj s

/-- The companion 1 - conj(rho) is also a zero of zeta. -/
lemma zeta_zero_implies_companion_zero (rho : Complex)
    (hzero : riemannZeta rho = 0)
    (hn : forall n : Nat, rho ≠ -↑n)
    (hone : rho ≠ 1) :
    riemannZeta (1 - starRingEnd Complex rho) = 0 := by
  have hfe : riemannZeta (1 - rho) = 0 :=
    zeta_zero_implies_fe_zero rho hzero hn hone
  have hconj : riemannZeta (starRingEnd Complex (1 - rho)) = 0 := by
    rw [GppRH.riemannZeta_conj, hfe]; simp
  have hid : starRingEnd Complex (1 - rho) = 1 - starRingEnd Complex rho := by
    simp [map_sub, map_one]
  rwa [hid] at hconj

/-- If zeta(rho) = 0 with rho in critical strip and Re(rho) != 1/2,
    then there are at least two distinct zeros at Im(rho). -/
theorem two_zeros_at_ordinate (rho : Complex)
    (hzero : riemannZeta rho = 0)
    (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hoffcr : rho.re ≠ 1 / 2) :
    exists rho' : Complex,
      rho' ≠ rho ∧ riemannZeta rho' = 0 ∧ rho'.im = rho.im := by
  refine ⟨1 - starRingEnd Complex rho, ?_, ?_, ?_⟩
  · exact companion_ne_of_off_critical rho hoffcr
  · apply zeta_zero_implies_companion_zero rho hzero
    · intro n heq
      have : rho.re = (-(↑n : Complex)).re := congr_arg Complex.re heq
      simp at this; linarith [hstrip.1]
    · intro heq
      have : rho.re = (1 : Complex).re := congr_arg Complex.re heq
      simp at this; linarith [hstrip.2]
  · exact companion_im_eq rho

/-! ## The pathway's target, as an actual theorem

`RHProofStructure.open_rh_pathway_target` parked the framework's RH route as a vacuous
`True` with the argument written out in a comment:

    Off-line zero ⟹ two distinct zeros at same ordinate ⟹
    total analytic multiplicity ≥ 2 ⟹ contradicts open_spectral_atom_weight_one.

That argument is entirely available here — `two_zeros_at_ordinate` above is the whole first
half and it is proved — so it is stated and proved below with the spectral input as an
explicit hypothesis rather than as a comment.

**Read the honest version of what this buys.** It is an *equivalence*, both directions
proved: RH on the strip holds **iff** each ordinate carries at most one strip zero. So this
does **not** advance RH by one inch. It relocates the entire difficulty into
`AtomWeightOne`, which is exactly where the framework already says it sits, and which is
still open — it needs trace-class theory for adèlic convolution operators, re-verified
absent from Mathlib 4.33.1 on 2026-09-01 (`Schatten`: zero hits; the 39 files a naive grep
returns are all `registerTraceClass`, Lean's debug tracing).

What it *does* buy is that the reduction is now machine-checked rather than asserted in a
comment, and the open input is visible in the signature of anything that uses it. That is
the same move that retired twelve physics axioms in `Link6`/`DMAbundance`.

The non-trivial content is the forward direction, and it is not formal shuffling: the
second zero at the same ordinate is produced by combining the functional equation with
`riemannZeta_conj` (proved above, via Mellin conjugation on the Hurwitz zeta), which is the
classical fact that off-line zeros come in quadruples. -/

/-- The companion `1 - conj ρ` of a critical-strip point is again in the critical strip,
    since `Re(1 - conj ρ) = 1 - Re ρ`. -/
lemma companion_mem_strip (rho : ℂ) (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    0 < (1 - starRingEnd ℂ rho).re ∧ (1 - starRingEnd ℂ rho).re < 1 := by
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  constructor <;> linarith

/-- **Atom weight one**: each ordinate carries at most one zero of `ζ` in the critical
    strip. This is `RHProofStructure.open_spectral_atom_weight_one`'s content, stated as a
    `Prop` to be *taken as a hypothesis* — deliberately not an axiom. -/
def AtomWeightOne : Prop :=
  ∀ r1 r2 : ℂ, riemannZeta r1 = 0 → riemannZeta r2 = 0 →
    0 < r1.re → r1.re < 1 → 0 < r2.re → r2.re < 1 → r1.im = r2.im → r1 = r2

/-- **The Riemann Hypothesis**, in the form the pathway targets: every zero of `ζ` in the
    open critical strip has real part `1/2`. (Every non-trivial zero lies in the strip, so
    this is the full statement.) -/
def RiemannHypothesisStrip : Prop :=
  ∀ r : ℂ, riemannZeta r = 0 → 0 < r.re → r.re < 1 → r.re = 1 / 2

/-- **Atom weight one implies RH.** The pathway's argument, machine-checked: an off-line
    strip zero `ρ` has the distinct companion `1 - conj ρ`, which `two_zeros_at_ordinate`
    shows is also a strip zero at the *same* ordinate — two zeros where the hypothesis
    permits one. -/
theorem rh_of_atomWeightOne (h : AtomWeightOne) : RiemannHypothesisStrip := by
  intro rho hzero h0 h1
  by_contra hne
  have hz' : riemannZeta (1 - starRingEnd ℂ rho) = 0 := by
    apply zeta_zero_implies_companion_zero rho hzero
    · intro n heq
      have : rho.re = (-(n : ℂ)).re := congr_arg Complex.re heq
      simp at this; linarith
    · intro heq
      have : rho.re = (1 : ℂ).re := congr_arg Complex.re heq
      simp at this; linarith
  obtain ⟨hs0, hs1⟩ := companion_mem_strip rho h0 h1
  exact companion_ne_of_off_critical rho hne
    (h _ _ hz' hzero hs0 hs1 h0 h1 (companion_im_eq rho))

/-- **RH implies atom weight one** — the converse, one line: two strip zeros at the same
    ordinate both have real part `1/2`, hence agree in both coordinates.

    Stated because it is what makes the honest claim about the direction above: the two
    statements are *equivalent*, so deriving RH from `AtomWeightOne` moves the difficulty
    rather than reducing it. -/
theorem atomWeightOne_of_rh (h : RiemannHypothesisStrip) : AtomWeightOne := by
  intro r1 r2 hz1 hz2 ha0 ha1 hb0 hb1 him
  exact Complex.ext (by rw [h r1 hz1 ha0 ha1, h r2 hz2 hb0 hb1]) him

/-- RH on the strip **iff** atom weight one. The pathway's target and its stated spectral
    input are the same statement; all the work is in establishing either one. -/
theorem rh_iff_atomWeightOne : RiemannHypothesisStrip ↔ AtomWeightOne :=
  ⟨atomWeightOne_of_rh, rh_of_atomWeightOne⟩

/-! ### `cor:simple-zeros`, and a distinction its statement elides

`RHProofStructure.open_zero_simplicity` reads *"every non-trivial zero of ζ is simple"*, with
the proof line "RH + spectral atom weight 1 ⟹ each ordinate has total multiplicity 1".

**Those are two different claims and the wording runs them together.**

* *One zero per ordinate* — the ordinate map is injective on the strip zero set. This follows
  from `AtomWeightOne` immediately, and is proved below.
* *Analytically simple* — each zero has order of vanishing exactly 1, i.e.
  `analyticOrderAt ζ ρ = 1`. This is **not** proved here and does not follow from
  `AtomWeightOne`: a single zero of order 2 sits at one ordinate and violates nothing above.

"Simple zero" in the literature means the second. The tree can honestly claim only the first,
so only the first is stated, and `open_zero_simplicity` stays for the second. Establishing it
needs Mathlib's `analyticOrderAt` API applied to ζ — available at 4.33.1, so this is a real
future target rather than a wall, but it is a separate theorem and not a corollary of what is
here. -/

/-- The zeros of ζ in the open critical strip. -/
def stripZeros : Set ℂ := {r | riemannZeta r = 0 ∧ 0 < r.re ∧ r.re < 1}

/-- **One zero per ordinate.** Under `AtomWeightOne` the ordinate map is injective on the
    strip zero set — the "total multiplicity 1" half of `cor:simple-zeros`.

    Not analytic simplicity: see the section note above. -/
theorem ordinate_injOn_of_atomWeightOne (h : AtomWeightOne) :
    Set.InjOn Complex.im stripZeros := by
  rintro r1 ⟨hz1, ha1, hb1⟩ r2 ⟨hz2, ha2, hb2⟩ him
  exact h r1 r2 hz1 hz2 ha1 hb1 ha2 hb2 him

/-- The contrapositive, in the form the pathway argument uses: two *distinct* strip zeros
    must sit at distinct ordinates. This is precisely what `two_zeros_at_ordinate`
    contradicts for an off-line zero. -/
theorem ordinate_ne_of_ne_of_atomWeightOne (h : AtomWeightOne)
    {r1 r2 : ℂ} (h1 : r1 ∈ stripZeros) (h2 : r2 ∈ stripZeros) (hne : r1 ≠ r2) :
    r1.im ≠ r2.im := fun him => hne (ordinate_injOn_of_atomWeightOne h h1 h2 him)

/-! ### Analytic simplicity: statable and reducible, but **not** reachable

`open_zero_simplicity`'s other half — each zero has order of vanishing exactly 1 — is stated
here and reduced to a concrete non-vanishing condition. Neither is a proof of it.

**Simplicity of the non-trivial zeros of ζ is an open problem in mathematics.** It is widely
believed, and a positive proportion of zeros is known simple (Conrey–Ghosh–Gonek and
successors), but the full statement is proved by no one. An earlier note in
`RHProofStructure.lean` called it "a real future target rather than a wall" on the grounds
that Mathlib has `analyticOrderAt`; that conflated *having the vocabulary to state a claim*
with *being able to prove it*, and is corrected there.

What follows is therefore infrastructure, not progress: it makes the claim expressible and
converts it into the form any attack would have to attack. -/

/-- **Analytic simplicity** of the critical-strip zeros: each has order of vanishing exactly
    one. This is what "simple zero" means in the literature, and it is *open*. -/
def SimpleStripZeros : Prop := ∀ r ∈ stripZeros, analyticOrderAt riemannZeta r = 1

/-- ζ is analytic at every strip zero — the pole at `s = 1` is outside the open strip. -/
private lemma zeta_analyticAt_of_strip {r : ℂ} (hr : r ∈ stripZeros) :
    AnalyticAt ℂ riemannZeta r := by
  have hne1 : r ≠ 1 := by
    intro h; rw [h] at hr; exact absurd hr.2.2 (by norm_num)
  exact analyticOn_riemannZeta r (by simpa using hne1)

/-- **Simplicity is exactly non-vanishing of `ζ'` at the zeros.**

    The useful direction is `←`: it turns a statement about orders of vanishing into a
    concrete non-vanishing condition on a single derivative, which is the form the analytic
    literature works in. The `→` direction is what makes it an equivalence rather than a
    convenience: if `ζ` and `ζ'` both vanish at `r` then the order is at least 2. -/
theorem simpleStripZeros_iff_deriv_ne_zero :
    SimpleStripZeros ↔ ∀ r ∈ stripZeros, deriv riemannZeta r ≠ 0 := by
  constructor
  · intro h r hr hderiv
    have hana := zeta_analyticAt_of_strip hr
    have h1 : analyticOrderAt riemannZeta r = 1 := h r hr
    have h2 : (2 : ℕ∞) ≤ analyticOrderAt riemannZeta r := by
      have hiff := natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 2) hana
      rw [show ((2 : ℕ) : ℕ∞) = (2 : ℕ∞) from rfl] at hiff
      rw [hiff]
      intro i hi
      interval_cases i
      · simpa using hr.1
      · simpa using hderiv
    rw [h1] at h2
    norm_num at h2
  · intro h r hr
    exact (zeta_analyticAt_of_strip hr).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      hr.1 (h r hr)

/-- K = A¹/Q* is compact. (Tate 1950) -/
theorem open_K_compact : True := by
  -- Placeholder: Full formalization requires Fujisaki's lemma / adelic topology in Mathlib.
  -- This is the compactness of the norm-1 idèle class group, standard in class field theory.
  -- See also HaarMeasure.lean sorries.
  trivial

/-- Haar-square convolution operators are positive trace-class on H_1.
    (vol(K) = 1, Hilbert-Schmidt, Reed-Simon VI.22) -/
theorem open_K_trace_class : True := by
  -- Placeholder for trace-class property of the convolution operator on L^{2}(K).
  -- Follows from compactness + Haar measure normalization.
  trivial

/-- Plancherel atom weight = 1 at each ordinate.
    (Fourier-Plancherel for (R+,x); 1D ODE eigenspace) -/
theorem open_plancherel_atom_one (_ : Real) : True := by
  -- Placeholder: The Plancherel measure on the principal series gives atom weight 1
  -- at each imaginary ordinate (corresponding to the 1-dimensional eigenspace of the
  -- infinitesimal generator). This is the key to multiplicity = 1 on the critical line.
  trivial

/-- Meyer spectral-Weil identity (Duke Math J 127, 2005).
    Hilbert atom weight at gamma = distributional zero count of zeta at gamma. -/
theorem open_meyer_spectral_weil (_ : Real) (_ : Nat) : True := by
  -- Placeholder: Equates the spectral side (Plancherel/Hilbert) with the
  -- distributional/Weil explicit formula side. Once both sides are formalized,
  -- this forces multiplicity contradiction off the line.
  trivial

/- RETIRED (2026-07-17): the `arithmetic_admissibility` axiom and its alias
   `riemann_hypothesis` formerly lived here. The axiom's statement was RH
   verbatim (every nontrivial zero has Re = 1/2), violating the standing rule
   of docs/FORMALIZATION_PLAN.md: no axiom asserting an open claim. It
   predates Thread D and is strictly superseded by the genuine conditional
     `GppWeilCriterion.rh_of_weil_pairedForm_nonneg`
   (RiemannHypothesis/WeilPositivityCriterion.lean): RH from the finite
   Weil-pairing positivity hypothesis — an actual mathematical condition,
   not RH restated. The AAC as a *mathematical condition* (temperedness of
   zero-evaluation functionals) remains the programme's target; see the
   temperedness scaffold below and SpectralWeil.lean. -/

/-- The integration functional exists as a continuous linear map on `SchwartzMap ℝ ℂ`.

    RETIRED AS AN AXIOM (this session): Mathlib v4.19.0 provides
    `SchwartzMap.integralCLM` (Analysis/Distribution/SchwartzSpace.lean:1110), the integral
    as a continuous linear map `𝓢(D, V) →L[𝕜] V`, for any measure with
    `HasTemperateGrowth`. On `ℝ`, `volume` is an additive Haar measure, so the instance
    `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth` (ibid.:600) applies and
    the witness is immediate; `integralCLM_apply` is a `rfl` lemma, so the defining equation
    needs no rewriting. This is now a theorem, proved, with no axiom. -/
theorem schwartz_integral_clm_exists :
    ∃ T : SchwartzMap ℝ ℂ →L[ℝ] ℂ,
      ∀ φ : SchwartzMap ℝ ℂ, T φ = ∫ u : ℝ, (φ u : ℂ) :=
  ⟨SchwartzMap.integralCLM ℝ volume, fun _ => rfl⟩

/-- **Exponential growth is not a tempered distribution.**

    RETIRED AS AN AXIOM (2026-08-31), and it was the last custom axiom in this repository.
    The proof is `ExpNotTempered.exp_growth_not_tempered` in
    `RiemannHypothesis/ExpNotTempered.lean`: a bump translated to `sign(a)·n` and scaled by
    `e^{-|a|n}` tends to zero in `𝓢(ℝ, ℂ)` (the shift costs only polynomial growth in the
    seminorms, the scalar decays exponentially), while its weighted integral is exactly
    translation-invariant. Continuity of `T` then forces a nonzero constant to be zero.

    It could not have been proved before this repository moved to Mathlib 4.33:
    `HasCompactSupport.toSchwartzMap`, which supplies the concrete nonzero Schwartz witness
    the argument needs, does not exist in 4.19.0. -/
theorem exp_growth_not_tempered (a : ℝ) (ha : a ≠ 0) :
    ¬∃ T : SchwartzMap ℝ ℂ →L[ℝ] ℂ,
      ∀ φ : SchwartzMap ℝ ℂ, T φ = ∫ u : ℝ, cexp (↑a * ↑u) * ↑(φ u) :=
  ExpNotTempered.exp_growth_not_tempered a ha

/-- Temperedness characterises the critical line. -/
theorem temperedness_iff_critical_line (a : ℝ) :
    (∃ T : SchwartzMap ℝ ℂ →L[ℝ] ℂ,
      ∀ φ : SchwartzMap ℝ ℂ, T φ = ∫ u : ℝ, cexp (↑a * ↑u) * ↑(φ u)) ↔
    a = 0 := by
  constructor
  · rintro hT
    by_contra ha
    exact exp_growth_not_tempered a ha hT
  · rintro rfl
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    exact schwartz_integral_clm_exists


end GppRH
