/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statements from Codex / GPT, audited by Turbo)
-/
import GppVerify.RiemannHypothesis.MobiusEchoPassivity
import GppVerify.RiemannHypothesis.SparseCutoffCriterion

/-!
# Möbius echo packet, item (4): the conditional composition

**Doubly conditional. This file does not prove the Riemann Hypothesis.** It composes two
already-merged results and keeps both open hypotheses visible in the statement:

* `GppSparseCutoff.riemannHypothesis_of_nat_subpower` (sparse-cutoff criterion): inequality (1),
  `EnergyZeroInequality Q A K`, together with subpower energy `Q(log N_j) ≤ N_j^η` along one
  sequence `N_j → ∞`, gives `RiemannHypothesis`.
* `GppMobiusEcho.sparse_energy_bound` (Möbius echo telescope): a storage/work law with subpower work
  gives that subpower energy for `Q = GppMobiusEcho.Q c`.

The two hypotheses that remain **open**:

1. `h1`: inequality (1) for `Q = GppMobiusEcho.Q c`. Open in Lean (checked on paper, two ways).
2. `hstep` + `hwork`: a storage/work law with subpower work along `N_j`. Open mathematics, and of
   RH strength; the trivial choice `stor = 0`, `w k = log((k+1)/k) b_k²` only restates the energy
   obligation.
-/

open Filter Topology

/-- Item (4) of the Möbius echo packet: conditional on inequality (1) for `Q = GppMobiusEcho.Q c`
and on a storage/work law with subpower work along a sequence `N_j → ∞`, the Riemann Hypothesis.
Both `h1` and `(hstep, hwork)` are open. -/
theorem rh_of_storage_work (c A K : ℝ) (hK : 0 < K)
    (h1 : GppSparseCutoff.EnergyZeroInequality (GppMobiusEcho.Q c) A K)
    (stor w : ℕ → ℝ) (Nj : ℕ → ℕ) (hNj : Tendsto Nj atTop atTop) (hN : ∀ j, 1 ≤ Nj j)
    (hS : ∀ k, 0 ≤ stor k)
    (hstep : ∀ j k, 1 ≤ k → k < Nj j →
      stor (k + 1) - stor k + Real.log ((k + 1 : ℝ) / k) * (GppMobiusEcho.b c k) ^ 2 ≤ w k)
    (hwork : ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
      stor 1 + ∑ k ∈ Finset.Ico 1 (Nj j), w k ≤ (Nj j : ℝ) ^ η) :
    RiemannHypothesis :=
  GppSparseCutoff.riemannHypothesis_of_nat_subpower h1 hK hNj
    (GppMobiusEcho.sparse_energy_bound c stor w Nj hN hS hstep hwork)
