/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statement pinned by Turbo, D4)
-/
import GppVerify.RiemannHypothesis.MobiusEchoPassivity

/-!
# The storage/work law is exactly subpower Möbius energy

 It records, as
a theorem, that the storage/work law (hypotheses `hstep`/`hwork` of `rh_of_storage_work`) adds no
content beyond subpower growth of the energy `Q_c` along one sequence.

For a **fixed** `c`, the following are equivalent:

* there are `stor w : ℕ → ℝ` (with `stor ≥ 0`) and `N_j → ∞` (all `N_j ≥ 1`) satisfying the
  storage/work law `hstep`, `hwork`;
* there is one sequence `N_j → ∞` (all `N_j ≥ 1`) with
  `∀ η > 0, ∀ᶠ j, Q_c (log N_j) ≤ N_j ^ η`.

Forward is `sparse_energy_bound`; reverse takes `stor = 0`, `w k = log((k+1)/k) · b_k²` and uses
`energy_identity`. The quantifier order is the pinned one: a single sequence first, not a fresh
subsequence per `η`. The direction "RH implies subpower energy" (at `c = 1/ζ(½)`) is a paper-level
partial-summation argument and is **not** part of this file.
-/

open Filter Topology

namespace GppMobiusEcho

/-- For fixed `c`: a storage/work law with subpower work along some `N_j → ∞` holds iff the energy
`Q_c(log N_j)` is subpower along some `N_j → ∞`. -/
theorem storage_work_iff_subpower_energy (c : ℝ) :
    (∃ (stor w : ℕ → ℝ) (Nj : ℕ → ℕ), Tendsto Nj atTop atTop ∧ (∀ j, 1 ≤ Nj j) ∧
      (∀ k, 0 ≤ stor k) ∧
      (∀ j k, 1 ≤ k → k < Nj j →
        stor (k + 1) - stor k + Real.log ((k + 1 : ℝ) / k) * (b c k) ^ 2 ≤ w k) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
        stor 1 + ∑ k ∈ Finset.Ico 1 (Nj j), w k ≤ (Nj j : ℝ) ^ η)) ↔
    (∃ Nj : ℕ → ℕ, Tendsto Nj atTop atTop ∧ (∀ j, 1 ≤ Nj j) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, Q c (Real.log (Nj j)) ≤ (Nj j : ℝ) ^ η) := by
  constructor
  · rintro ⟨stor, w, Nj, hNj, hN, hS, hstep, hwork⟩
    exact ⟨Nj, hNj, hN, sparse_energy_bound c stor w Nj hN hS hstep hwork⟩
  · rintro ⟨Nj, hNj, hN, hQ⟩
    refine ⟨fun _ => 0, fun k => Real.log ((k + 1 : ℝ) / k) * (b c k) ^ 2, Nj, hNj, hN,
      fun _ => le_refl _, ?_, ?_⟩
    · intro j k _ _
      simp
    · intro η hη
      filter_upwards [hQ η hη] with j hj
      rw [(energy_identity c (hN j)).2] at hj
      simpa using hj

end GppMobiusEcho

#print axioms GppMobiusEcho.storage_work_iff_subpower_energy
