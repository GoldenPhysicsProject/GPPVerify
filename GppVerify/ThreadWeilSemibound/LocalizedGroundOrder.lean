import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

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
  exact (hlam a).mono (hlam b) (Set.image_subset R (hS hab))

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

end GppWeilSemibound
