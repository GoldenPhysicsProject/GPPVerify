/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statement from Codex / GPT, audited by Turbo)
-/
import Mathlib.Tactic
import GppVerify.RiemannHypothesis.CausalKernels
import GppVerify.RiemannHypothesis.CausalTailEstimate
import GppVerify.RiemannHypothesis.CausalNormBounds
import GppVerify.RiemannHypothesis.CausalTransforms
import GppVerify.RiemannHypothesis.MobiusEchoRH
import GppVerify.RiemannHypothesis.SparseCutoffCriterion

/-!
# `EnergyZeroInequality` for the Möbius energy, unconditionally

**Final assembly of the causal proof.** Codex's causal proof (`causal_zero_bound.md`, Turbo-audited),
formalized in four parts, discharges the Lean-open hypothesis `h1` of `rh_of_storage_work` for every
real `c`:

`energyZeroInequality_causal (c) : GppSparseCutoff.EnergyZeroInequality (GppMobiusEcho.Q c) (5/2 + 9|c|) 18`.

It is the alternative-constants form of inequality (1) (not the sharper `A = (3|c|+1)/2`, `K = 3/2`
of the Hardy/Plancherel route). The proof applies Part A's `causal_tail_estimate` with
`k = GppCausalKernels.kk`, `h = hh c = w − cZ`, `B = GppMobiusEcho.B c`: Part B gives `h = k ⋆ B`
(`causal_identity_rconv`), Part D2 the norm bounds (`‖k‖₁ ≤ 18`, `‖h‖₂ ≤ 5/2 + 9|c|`), Part C the
transforms at a zero (`k̂(r) = 0`, `ĥ(r) = (r − 1/2)/(1 + r)⁴`). The case `r = 1/2` is trivial (the
weight vanishes).

**What this does and does not do.** `rh_of_storage_work_causal` below is `rh_of_storage_work` with
hypothesis (i) (inequality (1)) now *proved*. It is still **conditional on (ii)**, the storage/work law
with subpower work along `N_j → ∞`, which is open mathematics of RH strength.
-/

open MeasureTheory Set GppCausalKernels GppCausalNorms GppCausalTransforms Filter Topology

namespace GppCausalEnergy

theorem integrableOn_B_sq (c L : ℝ) : IntegrableOn (fun t => GppMobiusEcho.B c t ^ 2) (Ioc (0:ℝ) L) := by
  set N : ℕ := ⌈Real.exp L⌉₊ with hN
  have hN1 : 1 ≤ N := by
    rw [hN]; exact Nat.one_le_iff_ne_zero.2 (by
      have : 0 < Real.exp L := Real.exp_pos L
      exact (Nat.ceil_pos.2 this).ne')
  have hI := (GppMobiusEcho.energy_identity c hN1).1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hLle : L ≤ Real.log N := by
    have h1 : Real.exp L ≤ N := Nat.le_ceil _
    calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos L) h1
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hlog0).1 hI
  exact h2.mono_set (Ioc_subset_Ioc_right hLle)

/-- **`EnergyZeroInequality` for the Möbius energy, unconditionally** (Codex's causal proof, the
alternative constants `5/2 + 9|c|` and `18`): for every real `c`,
`EnergyZeroInequality (GppMobiusEcho.Q c) (5/2 + 9|c|) 18`. -/
theorem energyZeroInequality_causal (c : ℝ) :
    GppSparseCutoff.EnergyZeroInequality (GppMobiusEcho.Q c) (5 / 2 + 9 * |c|) 18 := by
  intro r hz hr L hL
  have hQnn : 0 ≤ Real.sqrt (GppMobiusEcho.Q c L) := Real.sqrt_nonneg _
  by_cases hr' : r = 1 / 2
  · have : GppSparseCutoff.zeroWeight r = 0 := by
      unfold GppSparseCutoff.zeroWeight
      rw [hr']; simp
    rw [this, zero_mul]
    have : 0 ≤ 5 / 2 + 9 * |c| := by positivity
    positivity
  · have hmain := GppCausalTail.causal_tail_estimate kk (hh c) (GppMobiusEcho.B c) L hL r hr
      measurable_kk (measurable_hh c) (measurable_B c) kk_L1_bound.1 (hh_sq_bound c).1
      (integrableOn_B_sq c L) (fun t ht => causal_identity_rconv c L ht)
      (lap_kk_at_zero hr hr' hz)
    have hlap : ‖∫ t : ℝ in Ioi 0, Complex.exp (-r * (t : ℂ)) * (hh c t : ℂ)‖ =
        ‖r - 1 / 2‖ / ‖1 + r‖ ^ 4 := by
      have := lap_hh_at_zero c hr hr' hz
      unfold lap at this
      rw [this, norm_div, norm_pow]
    rw [hlap] at hmain
    have hQ : ∫ t in Ioc (0:ℝ) L, GppMobiusEcho.B c t ^ 2 = GppMobiusEcho.Q c L := by
      unfold GppMobiusEcho.Q
      rw [intervalIntegral.integral_of_le hL]
    rw [hQ] at hmain
    have hh2 : Real.sqrt (∫ t in Ioi (0:ℝ), hh c t ^ 2) ≤ 5 / 2 + 9 * |c| := by
      have h := (hh_sq_bound c).2
      calc Real.sqrt (∫ t in Ioi (0:ℝ), hh c t ^ 2) ≤ Real.sqrt ((5 / 2 + 9 * |c|) ^ 2) :=
            Real.sqrt_le_sqrt h
        _ = 5 / 2 + 9 * |c| := Real.sqrt_sq (by positivity)
    have hk : (∫ s in Ioi (0:ℝ), |kk s|) * Real.sqrt (GppMobiusEcho.Q c L) ≤
        18 * Real.sqrt (GppMobiusEcho.Q c L) :=
      mul_le_mul_of_nonneg_right kk_L1_bound.2 hQnn
    have hw : GppSparseCutoff.zeroWeight r * Real.exp (r.re * L) =
        Real.sqrt (2 * r.re) * Real.exp (r.re * L) * (‖r - 1 / 2‖ / ‖1 + r‖ ^ 4) := by
      unfold GppSparseCutoff.zeroWeight; ring
    rw [hw]
    linarith


/-- `rh_of_storage_work` with hypothesis (i) discharged by `energyZeroInequality_causal`: Riemann's
Hypothesis follows from a storage/work law with subpower work along a sequence `N_j → ∞`.
-/
theorem rh_of_storage_work_causal (c : ℝ) (stor w : ℕ → ℝ) (Nj : ℕ → ℕ)
    (hNj : Tendsto Nj atTop atTop) (hN : ∀ j, 1 ≤ Nj j) (hS : ∀ k, 0 ≤ stor k)
    (hstep : ∀ j k, 1 ≤ k → k < Nj j →
      stor (k + 1) - stor k + Real.log ((k + 1 : ℝ) / k) * (GppMobiusEcho.b c k) ^ 2 ≤ w k)
    (hwork : ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
      stor 1 + ∑ k ∈ Finset.Ico 1 (Nj j), w k ≤ (Nj j : ℝ) ^ η) :
    RiemannHypothesis :=
  rh_of_storage_work c (5 / 2 + 9 * |c|) 18 (by norm_num) (energyZeroInequality_causal c)
    stor w Nj hNj hN hS hstep hwork

end GppCausalEnergy
