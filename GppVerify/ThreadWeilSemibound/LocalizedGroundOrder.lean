import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Localized Weil ground-energy: order infrastructure

`formalization_queue` item `1b12010b` ("Uniform localized Weil lower bound is equivalent to
global semiboundedness"). Suzuki's localized ground energy is
`λ_a := inf_{0 ≠ v ∈ C_c^∞(-a,a)} Q_W(v)/‖v‖₂²` (his Corollary 1.2). This file abstracts
`λ_a` purely as an order-theoretic object — a real-valued function of `a` that is antitone
because the test-function spaces `S_a` are nested — and proves, as pure order/filter facts,
exactly the three sub-claims the queue item asks for:

1. nesting of `S_a` forces `λ` antitone (`lam_antitone_of_isGLB_of_nested`);
2. a uniform global lower bound on the underlying quadratic form over *all* compactly
   supported test functions is equivalent to `λ` being bounded below
   (`globalBound_iff_bddBelow_range_lam`) — the exact abstract counterpart of
   `inf_{a>0} λ_a > -∞`, phrased via `BddBelow (Set.range lam)` rather than a literal
   `sInf` so as to avoid `Real.sInf`'s junk-value convention on sets unbounded below;
3. antitone + not bounded below forces `λ_a → -∞` as `a → ∞`
   (`antitone_tendsto_atBot_of_not_bddBelow`), a short direct filter argument.

## The sharp form (added 2026-09-02)

Sub-claim 2 as originally stated is an *existence* statement on both sides: some uniform `C`
works iff `Set.range lam` is bounded below at all. That leaves open the question the program
actually cares about — whether the **optimal** constants agree, or whether localizing loses
something in the limit. They agree, and nothing is lost:

4. `lowerBounds_global_eq_lowerBounds_range_lam` — the global ratio set `R '' ⋃ a, S a` and
   the family of localized ground energies `Set.range lam` have **literally the same lower
   bounds**. Everything below follows from that one set equality, which is why it is stated
   separately rather than inlined: `isGLB_global_iff_isGLB_range_lam` and
   `bddBelow_global_iff_bddBelow_range_lam` are then both `rw`s.
5. `lam_tendsto_globalGround` — `λ_a → λ_∞` where `λ_∞` is the *global* ground energy, the
   greatest lower bound of the ratio over all test functions at once. So the localized
   ground energies do not merely stay above some global bound; they converge to the exact
   global one.
6. `lam_tendsto_atBot_or_tendsto_ciInf` — the dichotomy this thread runs on, with no third
   case: an antitone `λ` either diverges to `-∞` or converges to `⨅ a, λ a`. There is no
   oscillation, no failure-to-converge, and no need to assume convergence anywhere
   downstream.

The upshot for the program: "uniform localized Weil lower bound ⟺ global semiboundedness"
is not merely an equivalence of two existence claims — the two optimal constants are the
same real number, reached as a limit. What remains open is entirely the analytic input
(that `λ_a` is a finite real for each fixed `a`), not the passage to the limit.

## What this file does NOT do

It does **not** define `Q_W`, the Weil quadratic form, `‖·‖₂`, or `S_a = C_c^∞(-a,a)` at
all — that is a much larger, currently-absent Mathlib development (no localized
compactly-supported-smooth-function machinery of that shape exists in Mathlib), and is not
attempted here. This file supplies only the *order-theoretic skeleton* the queue item
itself says is available "once `λ_a` is abstracted as nested infima": `S`, `R`, and `lam`
below are arbitrary — an abstract test-space family, an abstract ratio functional, and an
abstract ground-energy function tied to them by the `IsGLB` hypothesis. No claim is made
that Suzuki's actual `λ_a` for the real Weil operator satisfies these hypotheses' premises
(in particular, that it is a well-defined finite real number for every `a`, i.e. that the
infimum is itself bounded below at each fixed finite `a`) — establishing that is exactly
the open, hard analytic core of the Weil-Semiboundedness program, untouched here. No RH
claim, no positivity claim about the real Weil kernel, no axiom.
-/

namespace GppWeilSemibound

open Filter Set

variable {X : Type*}

/-- **(i) Nesting forces the localized ground energy antitone.** If test-function spaces
`S : ℝ → Set X` are nested (`Monotone S`, i.e. `a ≤ b → S a ⊆ S b`) and `lam a` is the
greatest lower bound of a ratio functional `R` over `S a` for every `a`, then `lam` is
antitone: a bigger test space can only lower (or leave unchanged) the infimum. Pure
consequence of `IsGLB.mono`, with no reference to what `R` or `S` concretely are. -/
theorem lam_antitone_of_isGLB_of_nested {S : ℝ → Set X} (hS : Monotone S) {R : X → ℝ}
    {lam : ℝ → ℝ} (hlam : ∀ a, IsGLB (R '' S a) (lam a)) : Antitone lam := by
  intro a b hab
  exact (hlam a).mono (hlam b) (Set.image_mono (hS hab))

/-- **(ii) Global uniform lower bound ⟺ `lam` bounded below.** A uniform constant `C`
witnessing `-C ≤ R v` for every `v` in every level `S a` exists if and only if
`Set.range lam` is bounded below — the precise abstract form of "`inf_{a>0} λ_a > -∞`",
avoiding `Real.sInf`'s junk value (`0`) on sets not bounded below by never taking a literal
infimum of a possibly-unbounded-below set. Since every compactly supported test function
lies in some `S_a` (any bounded support fits inside `(-a,a)` for large enough `a`), the
left side is exactly "`Q_W(v) ≥ -C‖v‖²` for every compactly supported smooth `v`" once `R`
and `S` are instantiated to the real Weil setting. -/
theorem globalBound_iff_bddBelow_range_lam {S : ℝ → Set X} {R : X → ℝ} {lam : ℝ → ℝ}
    (hlam : ∀ a, IsGLB (R '' S a) (lam a)) :
    (∃ C : ℝ, ∀ a, ∀ v ∈ S a, -C ≤ R v) ↔ BddBelow (Set.range lam) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨-C, ?_⟩
    rintro y ⟨a, rfl⟩
    exact (hlam a).2 (by rintro x ⟨v, hv, rfl⟩; exact hC a v hv)
  · rintro ⟨C, hC⟩
    refine ⟨-C, fun a v hv => ?_⟩
    have h1 : lam a ≤ R v := (hlam a).1 ⟨v, hv, rfl⟩
    have h2 : C ≤ lam a := hC ⟨a, rfl⟩
    linarith

/-- **(iii) Antitone + unbounded below ⟹ `λ_a → -∞`.** If `lam` is nonincreasing
(`Antitone`) and its range is not bounded below, then `lam` tends to `-∞` along `a → ∞`.
Direct filter argument: for any target `b`, unboundedness gives some `lam a₀ < b`, and
antitonicity keeps `lam a ≤ lam a₀ < b` for every `a ≥ a₀`. -/
theorem antitone_tendsto_atBot_of_not_bddBelow {lam : ℝ → ℝ} (hanti : Antitone lam)
    (hunbdd : ¬BddBelow (Set.range lam)) : Tendsto lam atTop atBot := by
  rw [tendsto_atBot]
  intro b
  obtain ⟨y, hy_mem, hy_lt⟩ := not_bddBelow_iff.mp hunbdd b
  obtain ⟨a0, rfl⟩ := hy_mem
  rw [eventually_atTop]
  exact ⟨a0, fun a ha => (hanti ha).trans hy_lt.le⟩

/-- **Assembled**: nesting, plus a witnessed failure of a global uniform bound, together
force `λ_a → -∞`. This is the queue item's three sub-claims chained into the single
"contrapositive" statement it was really after: if there is *no* finite `C` with
`Q_W(v) ≥ -C‖v‖²` on all compactly supported `v`, the localized ground energies must
diverge to `-∞`, not merely fail to have one specific uniform bound. -/
theorem tendsto_atBot_of_not_globalBound {S : ℝ → Set X} (hS : Monotone S) {R : X → ℝ}
    {lam : ℝ → ℝ} (hlam : ∀ a, IsGLB (R '' S a) (lam a))
    (hnobound : ¬∃ C : ℝ, ∀ a, ∀ v ∈ S a, -C ≤ R v) : Tendsto lam atTop atBot :=
  antitone_tendsto_atBot_of_not_bddBelow (lam_antitone_of_isGLB_of_nested hS hlam)
    (fun h => hnobound ((globalBound_iff_bddBelow_range_lam hlam).mpr h))

/-! ## The sharp form: the localized ground energies converge to the global one

Everything in this section rests on one set equality, `lowerBounds_global_eq_lowerBounds_-`
`range_lam`. It is worth isolating because it is strictly stronger than the equivalence
above: `globalBound_iff_bddBelow_range_lam` matches *existence* of a bound on each side,
while this matches the two sets of bounds themselves, so the optimal constants coincide
rather than merely both existing.
-/

/-- **The global ratio set and the localized ground energies have the same lower bounds.**

`x` bounds `R` from below on every test function at once iff `x ≤ λ_a` for every `a`. Left
to right: `x` bounds `R '' S a` below for each fixed `a`, and `λ_a` is the *greatest* such
bound. Right to left: any `v` lies in some `S a`, and `x ≤ λ_a ≤ R v`.

Note what is *not* assumed: no boundedness, no nonemptiness of the `S a`, and no finiteness
of any `λ_a` beyond the `IsGLB` hypothesis itself. -/
theorem lowerBounds_global_eq_lowerBounds_range_lam {S : ℝ → Set X} {R : X → ℝ}
    {lam : ℝ → ℝ} (hlam : ∀ a, IsGLB (R '' S a) (lam a)) :
    lowerBounds (R '' ⋃ a, S a) = lowerBounds (Set.range lam) := by
  ext x
  constructor
  · rintro hx y ⟨b, rfl⟩
    refine (hlam b).2 ?_
    rintro z ⟨v, hv, rfl⟩
    exact hx ⟨v, Set.mem_iUnion.mpr ⟨b, hv⟩, rfl⟩
  · rintro hx y ⟨v, hv, rfl⟩
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hv
    exact le_trans (hx ⟨a, rfl⟩) ((hlam a).1 ⟨v, ha, rfl⟩)

/-- A real number is the global ground energy iff it is the greatest lower bound of the
localized ones. Immediate from the lower-bound sets being equal, since `IsGLB s` is by
definition `IsGreatest (lowerBounds s)`. -/
theorem isGLB_global_iff_isGLB_range_lam {S : ℝ → Set X} {R : X → ℝ} {lam : ℝ → ℝ}
    (hlam : ∀ a, IsGLB (R '' S a) (lam a)) (L : ℝ) :
    IsGLB (R '' ⋃ a, S a) L ↔ IsGLB (Set.range lam) L := by
  unfold IsGLB IsGreatest
  rw [lowerBounds_global_eq_lowerBounds_range_lam hlam]

/-- The global ratio set is bounded below iff the localized ground energies are. This is
`globalBound_iff_bddBelow_range_lam` again, but derived from the set equality rather than
by two separate `linarith` arguments — and stated on the ratio set itself rather than
through an existential constant. -/
theorem bddBelow_global_iff_bddBelow_range_lam {S : ℝ → Set X} {R : X → ℝ} {lam : ℝ → ℝ}
    (hlam : ∀ a, IsGLB (R '' S a) (lam a)) :
    BddBelow (R '' ⋃ a, S a) ↔ BddBelow (Set.range lam) := by
  unfold BddBelow
  rw [lowerBounds_global_eq_lowerBounds_range_lam hlam]

/-- **The dichotomy the thread runs on.** An antitone `λ` either diverges to `-∞` or
converges to `⨅ a, λ a`. There is no third case — no oscillation, no bounded-but-divergent
behaviour — so nothing downstream needs to assume convergence. -/
theorem lam_tendsto_atBot_or_tendsto_ciInf {lam : ℝ → ℝ} (hanti : Antitone lam) :
    Tendsto lam atTop atBot ∨ Tendsto lam atTop (nhds (⨅ a, lam a)) := by
  by_cases h : BddBelow (Set.range lam)
  · exact Or.inr (tendsto_atTop_ciInf hanti h)
  · exact Or.inl (antitone_tendsto_atBot_of_not_bddBelow hanti h)

/-- **The localized ground energies converge to the global ground energy.**

If `L` is the greatest lower bound of the ratio over *all* test functions at once, then
`λ_a → L`. So localizing loses nothing in the limit: the optimal uniform constant is
approached exactly, not merely bounded.

This is the sharp form of the queue item. The hypothesis `IsGLB (R '' ⋃ a, S a) L` is what
"the global Weil form is semibounded with optimal constant `L`" abstracts to; the
conclusion is what "the localized bounds determine it" abstracts to. -/
theorem lam_tendsto_globalGround {S : ℝ → Set X} (hS : Monotone S) {R : X → ℝ}
    {lam : ℝ → ℝ} (hlam : ∀ a, IsGLB (R '' S a) (lam a)) {L : ℝ}
    (hL : IsGLB (R '' ⋃ a, S a) L) : Tendsto lam atTop (nhds L) := by
  have hL' := (isGLB_global_iff_isGLB_range_lam hlam L).mp hL
  have hbdd : BddBelow (Set.range lam) := ⟨L, hL'.1⟩
  have h := tendsto_atTop_ciInf (lam_antitone_of_isGLB_of_nested hS hlam) hbdd
  have hu : L = ⨅ i, lam i := hL'.unique (isGLB_ciInf hbdd)
  rwa [← hu] at h

end GppWeilSemibound
