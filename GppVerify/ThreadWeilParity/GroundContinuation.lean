import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuation of even ground under no parity crossing

`formalization_queue` item `0182d9cf` ("Continuation of even ground from small support under
no parity crossing"), Weil-Parity thread. Pure topology: if two continuous real functions on
a preconnected set never cross (are never equal), and one starts strictly below the other at
some point, it stays strictly below everywhere. The queue item's own framing:

  "Let lambdaPlus(a), lambdaMinus(a) be continuous real functions on a connected interval.
  If lambdaPlus(a0)<lambdaMinus(a0) at one point and lambdaPlus(a) != lambdaMinus(a) for
  every a, then lambdaPlus(a)<lambdaMinus(a) throughout."

Proof: if `lamPlus a ≥ lamMinus a` at some other point `a`, the two-function Intermediate
Value Theorem (`IsPreconnected.intermediate_value₂`) forces a crossing point between `a0`
and `a`, contradicting `hne`.

## What this file does NOT do

Formalizes only the pure topological/continuity core the queue item calls "pure
finite-dimensional topology." It does **not** package the "matrix-family corollary" the
item also describes (continuous Hermitian parity blocks with disjoint spectra retaining an
initially-even simple ground eigenvalue throughout a parameter interval) — that additional
step needs matrix eigenvalue continuity and a displacement-multiplicity simplicity lemma
neither built here nor elsewhere in this repo yet. It also does not supply "continuity and
Suzuki's small-`a` simple/even theorem" for the actual Weil family — per the queue item's
own instruction, those stay explicit hypotheses for whichever future file applies this
lemma to the real family. No axiom, no sorry.
-/

namespace GppWeilParity

open Set

/-- **No-crossing continuation**: continuous functions `lamPlus, lamMinus` on a preconnected
set `s` that are never equal on `s`, with `lamPlus a0 < lamMinus a0` at one point `a0 ∈ s`,
satisfy `lamPlus a < lamMinus a` for every `a ∈ s`. -/
theorem lamPlus_lt_lamMinus_of_ne_of_lt_of_preconnected {s : Set ℝ} (hs : IsPreconnected s)
    {lamPlus lamMinus : ℝ → ℝ} (hcp : ContinuousOn lamPlus s) (hcm : ContinuousOn lamMinus s)
    {a0 : ℝ} (ha0 : a0 ∈ s) (hlt0 : lamPlus a0 < lamMinus a0)
    (hne : ∀ a ∈ s, lamPlus a ≠ lamMinus a) :
    ∀ a ∈ s, lamPlus a < lamMinus a := by
  intro a ha
  rcases lt_or_ge (lamPlus a) (lamMinus a) with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx, hxeq⟩ := hs.intermediate_value₂ ha0 ha hcp hcm hlt0.le h
    exact hne x hx hxeq

/-- Interval specialization, matching the queue item's "connected interval" phrasing
directly: `Icc a0 a1` is preconnected in `ℝ`, so the hypothesis reduces to plain continuity
on the closed interval. -/
theorem lamPlus_lt_lamMinus_of_ne_of_lt_Icc {a0 a1 : ℝ} (hle : a0 ≤ a1)
    {lamPlus lamMinus : ℝ → ℝ} (hcp : ContinuousOn lamPlus (Icc a0 a1))
    (hcm : ContinuousOn lamMinus (Icc a0 a1)) (hlt0 : lamPlus a0 < lamMinus a0)
    (hne : ∀ a ∈ Icc a0 a1, lamPlus a ≠ lamMinus a) :
    ∀ a ∈ Icc a0 a1, lamPlus a < lamMinus a :=
  lamPlus_lt_lamMinus_of_ne_of_lt_of_preconnected isPreconnected_Icc hcp hcm
    (left_mem_Icc.mpr hle) hlt0 hne

end GppWeilParity
