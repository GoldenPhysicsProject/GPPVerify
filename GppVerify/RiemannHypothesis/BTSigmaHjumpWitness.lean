/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.BTSigmaLocalEuler

/-!
# BT-Σ: an explicit piecewise wavefunction discharging `hjump`

Ported from GPPDiscovery5 `lean/bt-sigma/BTSigmaHjumpWitness.lean` (`39bef94`), audited by
Turbo on GPP-bridge PR #11 (comment 6800991395 §1: PROVED, standard axioms, `finiteCut_BT3`
non-vacuous as stated).

* `hjump_witness` PROVED: for any finite list of real cut weights `w j` (`j < n`) and any
  cut points with `x 0 ≠ x 1`, `x n ≠ x (n+1)`, there is an explicit piecewise-`C¹` scalar
  path `ψ` with vanishing outer traces whose interior trace jumps are exactly `w j`.
* `finiteCut_BT3_witness` PROVED: hence the hypotheses of `finiteCut_BT3` are jointly
  satisfiable, and its conclusion holds for this `ψ`.

Scope, stated plainly: `ψ` is built from the weights alone. It does not use `f`, `U_p`, the
Tate vector or any vertex law. So this shows `finiteCut_BT3` is non-vacuous; it does **not**
show that the spec's `ψ_{f,W}` has these jumps for a structural reason. That provenance is
(P-LOG), still OPEN, in line with the (NC2) guard `amplitude_insertion_reproduces_weights`.

No `sorry`, no `admit`, no custom axiom. (P-LOG), (BT-Σ), ARP and RH remain **OPEN**.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the Cosmos / Grok).
Task and audit: Turbo.
-/

namespace GppBTSigmaHjumpWitness

open Complex GppBTSigmaLocalEuler
open scoped InnerProductSpace ContDiff

/-- Slack constant making every amplitude-squared nonnegative. -/
noncomputable def slack (n : ℕ) (w : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range n, |w i|

/-- Squared amplitude on piece `j`: slack plus the tail of the weights from `j`. -/
noncomputable def ampSq (n : ℕ) (w : ℕ → ℝ) (j : ℕ) : ℝ :=
  slack n w + ∑ i ∈ Finset.Ico j n, w i

theorem ampSq_nonneg (n : ℕ) (w : ℕ → ℝ) (j : ℕ) : 0 ≤ ampSq n w j := by
  unfold ampSq slack
  have h1 : ∑ i ∈ Finset.Ico j n, -|w i| ≤ ∑ i ∈ Finset.Ico j n, w i :=
    Finset.sum_le_sum fun i _ => neg_abs_le (w i)
  have h2 : ∑ i ∈ Finset.Ico j n, |w i| ≤ ∑ i ∈ Finset.range n, |w i| := by
    rw [Finset.range_eq_Ico]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico_left (Nat.zero_le j)) fun i _ _ => abs_nonneg (w i)
  rw [Finset.sum_neg_distrib] at h1
  linarith

theorem ampSq_jump (n : ℕ) (w : ℕ → ℝ) {j : ℕ} (hj : j < n) :
    ampSq n w j - ampSq n w (j + 1) = w j := by
  unfold ampSq
  rw [Finset.sum_eq_sum_Ico_succ_bot hj]
  ring

/-- Amplitude on piece `j`. -/
noncomputable def amp (n : ℕ) (w : ℕ → ℝ) (j : ℕ) : ℝ := Real.sqrt (ampSq n w j)

/-- The left ramp (on piece `0`) and right ramp (on piece `n`); `1` elsewhere. -/
noncomputable def ramp (n : ℕ) (x : ℕ → ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  (if j = 0 then (t - x 0) / (x 1 - x 0) else 1) *
    (if j = n then (x (n + 1) - t) / (x (n + 1) - x n) else 1)

/-- The explicit piecewise wavefunction. -/
noncomputable def psiW (n : ℕ) (w : ℕ → ℝ) (x : ℕ → ℝ) (j : ℕ) (t : ℝ) : ℂ :=
  ((amp n w j * ramp n x j t : ℝ) : ℂ)

theorem ramp_contDiff (n : ℕ) (x : ℕ → ℝ) (j : ℕ) : ContDiff ℝ 1 (ramp n x j) := by
  unfold ramp
  apply ContDiff.mul
  · split_ifs
    · exact (contDiff_id.sub contDiff_const).div_const _
    · exact contDiff_const
  · split_ifs
    · exact (contDiff_const.sub contDiff_id).div_const _
    · exact contDiff_const

theorem psiW_contDiff (n : ℕ) (w : ℕ → ℝ) (x : ℕ → ℝ) (j : ℕ) :
    ContDiff ℝ 1 (psiW n w x j) := by
  unfold psiW
  exact ofRealCLM.contDiff.comp (contDiff_const.mul (ramp_contDiff n x j))

theorem inner_ofReal_self (a : ℝ) : inner ℂ (a : ℂ) (a : ℂ) = ((a ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K, Complex.norm_real, Real.norm_eq_abs]
  have : ((|a| : ℝ) : ℂ) ^ 2 = ((a ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, sq_abs]
  exact this

theorem psiW_sq (n : ℕ) (w : ℕ → ℝ) (x : ℕ → ℝ) (j : ℕ) (t : ℝ)
    (hr : ramp n x j t = 1) :
    inner ℂ (psiW n w x j t) (psiW n w x j t) = ((ampSq n w j : ℝ) : ℂ) := by
  unfold psiW
  rw [hr, mul_one, inner_ofReal_self, amp, Real.sq_sqrt (ampSq_nonneg n w j)]

/-- **`hjump` witness.** PROVED. -/
theorem hjump_witness (n : ℕ) (w : ℕ → ℝ) (x : ℕ → ℝ) (h01 : x 0 ≠ x 1)
    (hnn : x n ≠ x (n + 1)) :
    (∀ j, ContDiff ℝ 1 (psiW n w x j)) ∧ psiW n w x 0 (x 0) = 0 ∧
      psiW n w x n (x (n + 1)) = 0 ∧
      ∀ j < n,
        inner ℂ (psiW n w x j (x (j + 1))) (psiW n w x j (x (j + 1))) -
          inner ℂ (psiW n w x (j + 1) (x (j + 1))) (psiW n w x (j + 1) (x (j + 1))) =
        ((w j : ℝ) : ℂ) := by
  have d01 : x 1 - x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h01)
  have dnn : x (n + 1) - x n ≠ 0 := sub_ne_zero.mpr (Ne.symm hnn)
  refine ⟨psiW_contDiff n w x, ?_, ?_, ?_⟩
  · simp [psiW, ramp]
  · simp [psiW, ramp]
  · intro j hj
    have hl : ramp n x j (x (j + 1)) = 1 := by
      unfold ramp
      rw [if_neg (by omega : j ≠ n)]
      split_ifs with h
      · subst h; simp [div_self d01]
      · simp
    have hr : ramp n x (j + 1) (x (j + 1)) = 1 := by
      unfold ramp
      rw [if_neg (by omega : j + 1 ≠ 0)]
      split_ifs with h
      · rw [h]; simp [div_self dnn]
      · simp
    rw [psiW_sq n w x j _ hl, psiW_sq n w x (j + 1) _ hr, ← ofReal_sub, ampSq_jump n w hj]

/-- **(J) finite-cut BT3 holds for an explicit `ψ`.** PROVED. Shows the hypotheses of
`finiteCut_BT3` are jointly satisfiable. The `ψ` is weight-built, not the spec's
`ψ_{f,W}`; provenance of the jumps is (P-LOG), OPEN. -/
theorem finiteCut_BT3_witness (S : Finset ℕ) (N : ℕ) (g : ℝ → ℝ) (W : ℝ) (n : ℕ)
    (σ : Fin n ≃ (cutIndex S N)) (x : ℕ → ℝ) (h01 : x 0 ≠ x 1) (hnn : x n ≠ x (n + 1)) :
    ∃ ψ : ℕ → ℝ → ℂ, (∀ j, ContDiff ℝ 1 (ψ j)) ∧ ψ 0 (x 0) = 0 ∧ ψ n (x (n + 1)) = 0 ∧
      ∑ j ∈ Finset.range (n + 1), (∫ t in x j..x (j + 1), greenIntegrand (ψ j) t) =
        I * (stratumSN S N g W : ℂ) := by
  let w : ℕ → ℝ := fun j => if h : j < n then cutWeight (σ ⟨j, h⟩) g W else 0
  obtain ⟨hψ, h0, hn, hj⟩ := hjump_witness n w x h01 hnn
  refine ⟨psiW n w x, hψ, h0, hn, finiteCut_BT3 S N g W n σ (psiW n w x) x hψ h0 hn ?_⟩
  intro j
  rw [hj j j.isLt]
  simp [w, j.isLt]

end GppBTSigmaHjumpWitness

