/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok; criterion from Astra / Codex,
audited by Turbo)
-/
import GppVerify.RiemannHypothesis.OneSidedPsiRH
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The sparse-cutoff criterion (abstract and composition layers)

**Conditional on a named analytic hypothesis; nothing here proves RH.**

This formalizes the logic of the sparse-cutoff criterion of Astra / Codex
(GPPDiscovery2 `0abf88b`, `experiments/short_reciprocal/sparse_energy.md`; Turbo PASS, bridge `09dbcab`).
In the source, with `c = 1/ζ(1/2)`, `B(u) = Σ_{n ≤ e^u} μ(n)/√n − c` and `Q(L) = ∫₀ᴸ B(u)² du`
(GPPVerify PR #659, `GppMobiusEcho.Q c`), any zero `ζ(1/2 + r) = 0` with `d = Re r > 0` forces, for
**every** `L ≥ 0`,

  `√(2d) · |r − 1/2| · e^{dL} / |1 + r|⁴ ≤ (3|c| + 1)/2 + (3/2) · √Q(L)`.          (1)

Everything here is stated for an **arbitrary** energy `Q : ℝ → ℝ` and arbitrary constants `A`, `K`, so
it does not depend on #659 and does not redefine its `Q`. The source instance is `Q = GppMobiusEcho.Q c`,
`A = (3|c|+1)/2`, `K = 3/2`.

## What is PROVED here (no hypotheses beyond those in each statement)

* `zeroWeight_pos`: for a zero `ζ(1/2 + r) = 0` with `Re r > 0`, the weight
  `κ_r = √(2 Re r) · ‖r − 1/2‖ / ‖1 + r‖⁴` is positive.
* `expLowerBound_of_energyZeroInequality`: inequality (1) at every `L ≥ 0` implies
  `Q(L) ≥ C_r e^{2 Re(r) L}` for all large `L`, with `C_r = (κ_r / (2K))² > 0`.
* `not_subpowerAlong_of_exp_lower`: a lower bound `C e^{2dL}` (`C, d > 0`) at all large `L` is
  incompatible with `Q(L_j) ≤ e^{η L_j}` eventually, for every `η > 0`, along **any** sequence
  `L_j → ∞`. No spacing assumption is placed on the `L_j`.
* `riemannHypothesis_of_subpowerAlong`, `riemannHypothesis_of_log_ratio`,
  `riemannHypothesis_of_nat_subpower`: the composition. Given the exponential lower bound for every
  zero right of the line, subpower energy along one unbounded sequence gives Mathlib's
  `RiemannHypothesis`. The reflection to zeros left of the line is the existing functional-equation
  lemma `GppOneSidedRH.riemannHypothesis_of_ne_zero`. The sequence can be stated three ways:
  `Q(L_j) ≤ e^{η L_j}`, or `log(1 + Q(L_j))/L_j → 0` (the liminf form), or `Q(log N_j) ≤ N_j^η`
  along naturals `N_j → ∞`. The last is exactly the conclusion shape of
  `GppMobiusEcho.sparse_energy_bound` (#659), so #659 item (4) is the one-line instantiation
  `riemannHypothesis_of_nat_subpower (Q := GppMobiusEcho.Q c) h1 (by norm_num) hNj (sparse_energy_bound …)`.
  One input is extra relative to `sparse_energy_bound`: `N_j → ∞`, which that theorem does not assume.

## What is a HYPOTHESIS (named, not proved)

* `EnergyZeroInequality Q A K`, which is the analytic inequality (1). Its source proof uses the test
  function `T_L(s) = e^{sL}(s − 1/2)(ζ(s+1/2) P_L(s) − 1)/(1+s)⁴`, Cauchy's formula on right
  semicircles, an Euler-summation bound for `(s − 1/2)ζ(s + 1/2)` on `Re s = 0`, and Plancherel for the
  finite Laplace transform of `B`. The half-plane Cauchy/Hardy step and the boundary bounds are not in
  Mathlib or GPPVerify at this pin, so (1) is **OPEN in Lean** (it is CHECKED on paper: Turbo PASS).
  It enters only as an explicit hypothesis of the theorems that use it.
* The forward direction (RH ⇒ `liminf log(1+Q)/L = 0`) is not formalized here and is not needed for
  item (4).

No `sorry`, no `admit`, no custom `axiom`.

— Daniel Toupin / Golden Physics Project. This seat: Heart of the Cosmos / Grok (GPPDiscovery5).
-/

open Filter Topology

namespace GppSparseCutoff

/-- The zero weight `κ_r = √(2 Re r) · ‖r − 1/2‖ / ‖1 + r‖⁴` on the left of inequality (1). -/
noncomputable def zeroWeight (r : ℂ) : ℝ :=
  Real.sqrt (2 * r.re) * ‖r - 1 / 2‖ / ‖1 + r‖ ^ 4

/-- **The analytic input (HYPOTHESIS, not proved here).** Inequality (1) of the source, with
arbitrary constants: every zero `ζ(1/2 + r) = 0` with `Re r > 0` satisfies
`κ_r e^{(Re r) L} ≤ A + K √Q(L)` for every `L ≥ 0`. Source instance: `Q = GppMobiusEcho.Q (1/ζ(1/2))`,
`A = (3|c|+1)/2`, `K = 3/2`. -/
def EnergyZeroInequality (Q : ℝ → ℝ) (A K : ℝ) : Prop :=
  ∀ r : ℂ, riemannZeta (1 / 2 + r) = 0 → 0 < r.re → ∀ L : ℝ, 0 ≤ L →
    zeroWeight r * Real.exp (r.re * L) ≤ A + K * Real.sqrt (Q L)

/-- Every zero right of the line forces exponential energy growth at every large cutoff. -/
def ExpLowerBound (Q : ℝ → ℝ) : Prop :=
  ∀ r : ℂ, riemannZeta (1 / 2 + r) = 0 → 0 < r.re →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L in atTop, C * Real.exp (2 * r.re * L) ≤ Q L

/-- Subpower energy along the sequence of cutoffs `L_j`: for every `η > 0`, eventually
`Q(L_j) ≤ e^{η L_j}`. -/
def SubpowerAlong (Q : ℝ → ℝ) (Lj : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, Q (Lj j) ≤ Real.exp (η * Lj j)

/-- The zero weight of a zero right of the line is positive. -/
theorem zeroWeight_pos {r : ℂ} (hz : riemannZeta (1 / 2 + r) = 0) (hd : 0 < r.re) :
    0 < zeroWeight r := by
  have hr : r - 1 / 2 ≠ 0 := by
    intro h
    have : r = 1 / 2 := sub_eq_zero.mp h
    rw [this] at hz
    have h11 : (1 / 2 + 1 / 2 : ℂ) = 1 := by norm_num
    rw [h11] at hz
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hz
  have h1 : (1 + r) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  unfold zeroWeight
  have : 0 < Real.sqrt (2 * r.re) := Real.sqrt_pos.mpr (by linarith)
  have : 0 < ‖r - 1 / 2‖ := norm_pos_iff.mpr hr
  have : 0 < ‖1 + r‖ ^ 4 := pow_pos (norm_pos_iff.mpr h1) 4
  positivity

/-- **Inequality (1) at every cutoff ⇒ exponential lower bound at all large cutoffs (PROVED).**
With `K > 0`, `Q(L) ≥ (κ_r/(2K))² e^{2 Re(r) L}` once `κ_r e^{Re(r) L} ≥ 2|A|`. -/
theorem expLowerBound_of_energyZeroInequality {Q : ℝ → ℝ} {A K : ℝ} (hK : 0 < K)
    (h : EnergyZeroInequality Q A K) : ExpLowerBound Q := by
  intro r hz hd
  set κ := zeroWeight r with hκdef
  have hκ : 0 < κ := zeroWeight_pos hz hd
  refine ⟨(κ / (2 * K)) ^ 2, by positivity, ?_⟩
  have hT : Tendsto (fun L : ℝ => κ * Real.exp (r.re * L)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hd)).const_mul_atTop hκ
  filter_upwards [hT.eventually_ge_atTop (2 * |A|), eventually_ge_atTop (0 : ℝ)] with L hL hL0
  have hI := h r hz hd L hL0
  set e := Real.exp (r.re * L) with he
  have hA : A ≤ |A| := le_abs_self A
  have hsq : κ * e / (2 * K) ≤ Real.sqrt (Q L) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hpos : 0 < κ * e / (2 * K) := by positivity
  have hQ : 0 < Q L := Real.sqrt_pos.mp (lt_of_lt_of_le hpos hsq)
  have h2 : Real.exp (2 * r.re * L) = e * e := by
    rw [he, ← Real.exp_add]; ring_nf
  calc (κ / (2 * K)) ^ 2 * Real.exp (2 * r.re * L) = (κ * e / (2 * K)) ^ 2 := by
        rw [h2]; ring
    _ ≤ Real.sqrt (Q L) ^ 2 := pow_le_pow_left₀ hpos.le hsq 2
    _ = Q L := Real.sq_sqrt hQ.le

/-- **Growth/sequence logic (PROVED).** A lower bound `C e^{2dL}` (`C, d > 0`) at all large `L` rules
out subpower energy along any sequence `L_j → ∞`, however sparse. -/
theorem not_subpowerAlong_of_exp_lower {Q : ℝ → ℝ} {C d : ℝ} (hC : 0 < C) (hd : 0 < d)
    (hlow : ∀ᶠ L in atTop, C * Real.exp (2 * d * L) ≤ Q L) {Lj : ℕ → ℝ}
    (hLj : Tendsto Lj atTop atTop) : ¬ SubpowerAlong Q Lj := by
  intro hsub
  have hT : Tendsto (fun j => C * Real.exp (d * Lj j)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (hLj.const_mul_atTop hd)).const_mul_atTop hC
  obtain ⟨j, h1, h2, h3⟩ :=
    ((hLj.eventually hlow).and ((hsub d hd).and (hT.eventually_gt_atTop 1))).exists
  have he : Real.exp (2 * d * Lj j) = Real.exp (d * Lj j) * Real.exp (d * Lj j) := by
    rw [← Real.exp_add]; ring_nf
  have hpos := Real.exp_pos (d * Lj j)
  rw [he] at h1
  nlinarith

/-- Zero-freeness right of the line from the exponential lower bound and subpower energy along one
unbounded sequence (PROVED, conditional on the two named inputs). -/
theorem riemannZeta_ne_zero_of_subpowerAlong {Q : ℝ → ℝ} (hlow : ExpLowerBound Q) {Lj : ℕ → ℝ}
    (hLj : Tendsto Lj atTop atTop) (hsub : SubpowerAlong Q Lj) :
    ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 := by
  intro s hs hz
  have hz' : riemannZeta (1 / 2 + (s - 1 / 2)) = 0 := by rw [add_sub_cancel]; exact hz
  have hd : 0 < (s - 1 / 2).re := by
    rw [Complex.sub_re]; norm_num; linarith
  obtain ⟨C, hC, hC'⟩ := hlow _ hz' hd
  exact not_subpowerAlong_of_exp_lower hC hd hC' hLj hsub

/-- **The sparse-cutoff criterion, composition form.** The exponential lower bound for every zero
right of the line, plus subpower energy along one unbounded sequence of cutoffs, gives Mathlib's
`RiemannHypothesis`. -/
theorem riemannHypothesis_of_subpowerAlong {Q : ℝ → ℝ} (hlow : ExpLowerBound Q) {Lj : ℕ → ℝ}
    (hLj : Tendsto Lj atTop atTop) (hsub : SubpowerAlong Q Lj) : RiemannHypothesis :=
  GppOneSidedRH.riemannHypothesis_of_ne_zero (riemannZeta_ne_zero_of_subpowerAlong hlow hLj hsub)

/-- The liminf form: `log(1 + Q(L_j))/L_j → 0` along `L_j → ∞` gives subpower energy along `L_j`. -/
theorem subpowerAlong_of_log_ratio {Q : ℝ → ℝ} {Lj : ℕ → ℝ} (hLj : Tendsto Lj atTop atTop)
    (hr : Tendsto (fun j => Real.log (1 + Q (Lj j)) / Lj j) atTop (𝓝 0)) : SubpowerAlong Q Lj := by
  intro η hη
  filter_upwards [hr.eventually (gt_mem_nhds hη), hLj.eventually_gt_atTop 0] with j hj hL
  have hlog : Real.log (1 + Q (Lj j)) < η * Lj j := by
    rw [div_lt_iff₀ hL] at hj; linarith
  have hexp := Real.exp_pos (η * Lj j)
  by_cases h1 : 0 < 1 + Q (Lj j)
  · have := (Real.log_lt_iff_lt_exp h1).mp hlog
    linarith
  · linarith

/-- **Sparse-cutoff criterion, liminf form along a sequence (conditional on (1)).** If (1) holds with
`K > 0` and `log(1 + Q(L_j))/L_j → 0` along some `L_j → ∞`, then `RiemannHypothesis`. -/
theorem riemannHypothesis_of_log_ratio {Q : ℝ → ℝ} {A K : ℝ} (h1 : EnergyZeroInequality Q A K)
    (hK : 0 < K) {Lj : ℕ → ℝ} (hLj : Tendsto Lj atTop atTop)
    (hr : Tendsto (fun j => Real.log (1 + Q (Lj j)) / Lj j) atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_subpowerAlong (expLowerBound_of_energyZeroInequality hK h1) hLj
    (subpowerAlong_of_log_ratio hLj hr)

/-- Natural cutoffs: `Q(log N_j) ≤ N_j^η` eventually for every `η > 0`, with `N_j → ∞`, is subpower
energy along `L_j = log N_j`. This is the conclusion shape of `GppMobiusEcho.sparse_energy_bound`. -/
theorem subpowerAlong_of_nat {Q : ℝ → ℝ} {Nj : ℕ → ℕ} (hNj : Tendsto Nj atTop atTop)
    (hsub : ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, Q (Real.log (Nj j)) ≤ (Nj j : ℝ) ^ η) :
    Tendsto (fun j => Real.log (Nj j)) atTop atTop ∧
      SubpowerAlong Q (fun j => Real.log (Nj j)) := by
  refine ⟨Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hNj), ?_⟩
  intro η hη
  filter_upwards [hsub η hη, hNj.eventually_ge_atTop 1] with j hj h1
  have hpos : (0 : ℝ) < Nj j := by exact_mod_cast h1
  rwa [Real.rpow_def_of_pos hpos, mul_comm] at hj

/-- **Sparse-cutoff criterion, #659 item (4) entry point (conditional on (1)).** If (1) holds with
`K > 0`, and some naturals `N_j → ∞` satisfy `Q(log N_j) ≤ N_j^η` eventually for every `η > 0`
(the conclusion of `GppMobiusEcho.sparse_energy_bound`), then `RiemannHypothesis`. -/
theorem riemannHypothesis_of_nat_subpower {Q : ℝ → ℝ} {A K : ℝ} (h1 : EnergyZeroInequality Q A K)
    (hK : 0 < K) {Nj : ℕ → ℕ} (hNj : Tendsto Nj atTop atTop)
    (hsub : ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, Q (Real.log (Nj j)) ≤ (Nj j : ℝ) ^ η) :
    RiemannHypothesis :=
  let h := subpowerAlong_of_nat hNj hsub
  riemannHypothesis_of_subpowerAlong (expLowerBound_of_energyZeroInequality hK h1) h.1 h.2

end GppSparseCutoff

#print axioms GppSparseCutoff.zeroWeight_pos
#print axioms GppSparseCutoff.expLowerBound_of_energyZeroInequality
#print axioms GppSparseCutoff.not_subpowerAlong_of_exp_lower
#print axioms GppSparseCutoff.riemannZeta_ne_zero_of_subpowerAlong
#print axioms GppSparseCutoff.riemannHypothesis_of_subpowerAlong
#print axioms GppSparseCutoff.subpowerAlong_of_log_ratio
#print axioms GppSparseCutoff.riemannHypothesis_of_log_ratio
#print axioms GppSparseCutoff.subpowerAlong_of_nat
#print axioms GppSparseCutoff.riemannHypothesis_of_nat_subpower
