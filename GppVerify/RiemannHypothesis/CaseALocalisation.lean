/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

/-!
# Case A of the 2-plane localisation: the analytic estimates, in the form they are used

Turbo (PR #11, 6818314460), question 1: formalise the Case A estimates, (i) the on-line bound
`K_on(t0, w)` independent of `L`, and (ii) the suppression of zeros with `β' ≤ β0`.

What is formalised here (all PROVED, Mathlib only):
* `phase_shift_norm`: for real `γ`, translating a bump by `s` only multiplies its transform by
  the unimodular phase `e^{iγs}`. So the size of an end bump's transform at an on-line zero
  does not depend on where the bump sits, i.e. it is independent of the window `L`.
* `online_block_bound`: unit-block zero counting `#{γ ∈ [n, n+1)} ≤ A log(n+2) + B` (a named
  HYPOTHESIS here: the unconditional Riemann–von Mangoldt local count, not in Mathlib) plus
  bump decay `≤ C/(n+1)^3` per zero in block `n` give a summable on-line mass with explicit
  total `≤ (A+B)·C·∑ 1/(n+1)^2`, a constant with no `L` in it. This is `K_on`.
* `low_level_suppressed`: zeros with `β' < β0` (weight `≤ K_low e^{δ'L}`, `δ' < δ`) lose to any
  fixed fraction `ε e^{δL}` of the block once `L > log((K_low+1)/ε)/(δ−δ')`.
* `caseA_claim_fails`: assembly. Block `≤ −c e^{δL}`, same-level zeros `≤ d e^{δL}` with
  `d < c` (resolution), on-line `≤ K_on`, lower-level `≤ K_low e^{δ'L}`: then `Q ≥ 0` on
  `ker ℓ_c` fails at every `L` above an explicit threshold.

Not formalised (stays SKETCH): the bump-decay constant `C` and the same-level constant `d`
as functions of `(ψ, w, t0, η0)`, and the main-term computation `F(γ0) ≈ E(α+iβ)`.
The counting input stays a named hypothesis. ARP OPEN, RH OPEN.
-/

namespace GppCaseALocalisation

open Complex MeasureTheory

/-- Translation by `s` multiplies the transform at a real frequency by a unimodular phase. -/
theorem phase_shift_norm (g : ℝ → ℂ) (γ s : ℝ) :
    ‖∫ y, g y * exp (↑(γ * (y + s)) * I)‖ = ‖∫ y, g y * exp (↑(γ * y) * I)‖ := by
  have h : ∀ y : ℝ, g y * exp (↑(γ * (y + s)) * I) =
      exp (↑(γ * s) * I) * (g y * exp (↑(γ * y) * I)) := by
    intro y
    rw [show (γ * (y + s) : ℝ) = γ * y + γ * s by ring, ofReal_add, add_mul, exp_add]
    ring
  simp_rw [h]
  rw [integral_const_mul, norm_mul, norm_exp_ofReal_mul_I, one_mul]

theorem log_le_succ (n : ℕ) : Real.log ((n : ℝ) + 2) ≤ (n : ℝ) + 1 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) + 2 by positivity)
  linarith

theorem summable_inv_sq_succ : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  simpa [Nat.cast_add, Nat.cast_one] using h

/-- The on-line bound `K_on`: per-block mass bound with no window parameter in it. -/
theorem mass_le (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (n : ℕ) (cnt m : ℝ)
    (hcnt : cnt ≤ A * Real.log ((n : ℝ) + 2) + B)
    (hm : m ≤ cnt * (C / ((n : ℝ) + 1) ^ 3)) :
    m ≤ (A + B) * C * (1 / ((n : ℝ) + 1) ^ 2) := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hc1 : cnt ≤ (A + B) * ((n : ℝ) + 1) := by
    have := log_le_succ n
    nlinarith [mul_le_mul_of_nonneg_left this hA]
  have hq : 0 ≤ C / ((n : ℝ) + 1) ^ 3 := by positivity
  calc m ≤ cnt * (C / ((n : ℝ) + 1) ^ 3) := hm
    _ ≤ (A + B) * ((n : ℝ) + 1) * (C / ((n : ℝ) + 1) ^ 3) :=
        mul_le_mul_of_nonneg_right hc1 hq
    _ = (A + B) * C * (1 / ((n : ℝ) + 1) ^ 2) := by
        field_simp

theorem online_block_bound (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (cnt mass : ℕ → ℝ)
    (hcnt : ∀ n, cnt n ≤ A * Real.log ((n : ℝ) + 2) + B)
    (hmass0 : ∀ n, 0 ≤ mass n) (hmass : ∀ n, mass n ≤ cnt n * (C / ((n : ℝ) + 1) ^ 3)) :
    Summable mass ∧
      ∑' n, mass n ≤ (A + B) * C * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
  have hle : ∀ n, mass n ≤ (A + B) * C * (1 / ((n : ℝ) + 1) ^ 2) := fun n =>
    mass_le A B C hA hB hC n (cnt n) (mass n) (hcnt n) (hmass n)
  have hs : Summable (fun n : ℕ => (A + B) * C * (1 / ((n : ℝ) + 1) ^ 2)) :=
    summable_inv_sq_succ.mul_left _
  have hsm : Summable mass := Summable.of_nonneg_of_le hmass0 hle hs
  refine ⟨hsm, ?_⟩
  rw [← tsum_mul_left]
  exact hsm.tsum_le_tsum hle hs

theorem exp_gain_beats (c K δ L : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hL : Real.log ((K + 1) / c) / δ < L) : K < c * Real.exp (δ * L) := by
  have h1 : Real.log ((K + 1) / c) < δ * L := by
    rw [div_lt_iff₀ hδ] at hL; linarith [mul_comm L δ]
  have hp : 0 < (K + 1) / c := div_pos (by linarith) hc
  have h2 : (K + 1) / c < Real.exp (δ * L) := by
    rw [← Real.exp_log hp]; exact Real.exp_lt_exp.2 h1
  rw [div_lt_iff₀ hc] at h2
  linarith [mul_comm (Real.exp (δ * L)) c]

/-- Part (ii): zeros strictly below the level `β0` die against the block. -/
theorem low_level_suppressed (ε K δ δ' L : ℝ) (hε : 0 < ε) (hK : 0 ≤ K) (hδ : δ' < δ)
    (hL : Real.log ((K + 1) / ε) / (δ - δ') < L) :
    K * Real.exp (δ' * L) < ε * Real.exp (δ * L) := by
  have h := exp_gain_beats ε K (δ - δ') L hε hK (by linarith) hL
  have he : Real.exp (δ * L) = Real.exp ((δ - δ') * L) * Real.exp (δ' * L) := by
    rw [← Real.exp_add]; ring_nf
  rw [he, ← mul_assoc]
  exact mul_lt_mul_of_pos_right h (Real.exp_pos _)

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem no_negative_plane (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (lc : E →ₗ[ℝ] ℝ)
    (h : ∀ v, lc v = 0 → 0 ≤ B v v) (u w : E) :
    ¬ (∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → B (a • u + b • w) (a • u + b • w) < 0) := by
  intro hneg
  by_cases hz : lc w = 0 ∧ lc u = 0
  · have := hneg 1 0 (Or.inl one_ne_zero)
    simp only [one_smul, zero_smul, add_zero] at this
    exact absurd (h u hz.2) (not_le.2 this)
  · have hab : lc w ≠ 0 ∨ -lc u ≠ 0 := by
      by_contra hc; push Not at hc; exact hz ⟨hc.1, neg_eq_zero.1 hc.2⟩
    have hk : lc (lc w • u + (-lc u) • w) = 0 := by
      simp only [map_add, map_smul, smul_eq_mul]; ring
    exact absurd (h _ hk) (not_le.2 (hneg _ _ hab))

theorem sq_add_sq_pos {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) : 0 < a ^ 2 + b ^ 2 := by
  rcases hab with h | h
  · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg b]
  · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg a]

/-- Case A assembly: block, same-level, on-line and lower-level parts with explicit window. -/
theorem caseA_claim_fails (Bq Rs Ron Rlow : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (lc : E →ₗ[ℝ] ℝ) (u w : E)
    (c d Kon Klow δ δ' L : ℝ) (hdc : d < c) (hKon : 0 ≤ Kon) (hKlow : 0 ≤ Klow)
    (hδ : 0 < δ) (hδ' : δ' < δ)
    (hL1 : Real.log ((Kon + 1) / ((c - d) / 2)) / δ < L)
    (hL2 : Real.log ((Klow + 1) / ((c - d) / 2)) / (δ - δ') < L)
    (hq : ∀ a b : ℝ, Bq (a • u + b • w) (a • u + b • w) ≤
      -(c * Real.exp (δ * L)) * (a ^ 2 + b ^ 2))
    (hs : ∀ a b : ℝ, Rs (a • u + b • w) (a • u + b • w) ≤
      d * Real.exp (δ * L) * (a ^ 2 + b ^ 2))
    (hon : ∀ a b : ℝ, Ron (a • u + b • w) (a • u + b • w) ≤ Kon * (a ^ 2 + b ^ 2))
    (hlow : ∀ a b : ℝ, Rlow (a • u + b • w) (a • u + b • w) ≤
      Klow * Real.exp (δ' * L) * (a ^ 2 + b ^ 2)) :
    ¬ ∀ v, lc v = 0 → 0 ≤ (Bq + Rs + Ron + Rlow) v v := by
  intro h
  have hc2 : 0 < (c - d) / 2 := by linarith
  have h1 := exp_gain_beats _ Kon δ L hc2 hKon hδ hL1
  have h2 := low_level_suppressed _ Klow δ δ' L hc2 hKlow hδ' hL2
  have he := Real.exp_pos (δ * L)
  refine no_negative_plane (Bq + Rs + Ron + Rlow) lc h u w ?_
  intro a b hab
  have hp := sq_add_sq_pos hab
  have e1 := hq a b; have e2 := hs a b; have e3 := hon a b; have e4 := hlow a b
  simp only [LinearMap.add_apply]
  have key : (d * Real.exp (δ * L) + Kon + Klow * Real.exp (δ' * L)) <
      c * Real.exp (δ * L) := by nlinarith
  nlinarith [mul_lt_mul_of_pos_right key hp]

end GppCaseALocalisation

#print axioms GppCaseALocalisation.phase_shift_norm
#print axioms GppCaseALocalisation.log_le_succ
#print axioms GppCaseALocalisation.summable_inv_sq_succ
#print axioms GppCaseALocalisation.mass_le
#print axioms GppCaseALocalisation.online_block_bound
#print axioms GppCaseALocalisation.exp_gain_beats
#print axioms GppCaseALocalisation.low_level_suppressed
#print axioms GppCaseALocalisation.no_negative_plane
#print axioms GppCaseALocalisation.sq_add_sq_pos
#print axioms GppCaseALocalisation.caseA_claim_fails
