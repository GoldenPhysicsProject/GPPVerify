/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statements from Heart of the Cosmos / Grok)
-/
import Mathlib.Tactic
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Dirichlet-type liminf for `Σ w_k (1 − cos γ_k L)` (Round 23 F8)

For weights `w_k ≥ 0` with `Σ w_k < ∞` and arbitrary real `γ_k`,
`liminf_{L → ∞} Σ_k w_k (1 − cos γ_k L) = 0`. Formally: the sum is `≥ 0` for every `L`, and for
every `ε > 0` and every `T` there is `L ≥ T` at which it is `< ε`.

**Route (return-time step explicit, per Turbo's audit).** For a fixed step `T > 0` and a finite
head `k < N`, the points `x_j = (j T γ_k mod 2π)_{k<N}` of the compact torus `(ℝ/2πℤ)^N` have a
Cauchy subsequence, so two of them `x_i, x_j` (`i < j`) are within `δ` coordinatewise. Then
`L = (j − i) T ≥ T` returns every head phase `γ_k L` to within `δ` of `2π ℤ`. The step `T` is
arbitrary, so the return times are unbounded: no one-dimensional Dirichlet bound is used and no
bounded-return-time subtlety arises. The tail is uniform in `L`: `Σ_{k ≥ N} w_k (1 − cos) ≤
2 Σ_{k ≥ N} w_k`.

No zeta zero is an input; no `sorry`, no `axiom`.
-/

namespace GppHeartDirichlet

open Filter Topology

/-- Simultaneous return: for any finite family of phases and any step `T > 0`, some multiple
`L = jT` with `j ≥ 1` returns every phase `k < N` to within `δ` of `2π ℤ`. -/
theorem simultaneous_return (N : ℕ) (γ : ℕ → ℝ) {T δ : ℝ} (hδ : 0 < δ) :
    ∃ j : ℕ, 1 ≤ j ∧ ∀ k < N, ∃ m : ℤ, |(j : ℝ) * T * γ k - 2 * Real.pi * m| < δ := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let x : ℕ → (Fin N → AddCircle (2 * Real.pi)) :=
    fun j k => (((j : ℝ) * T * γ k : ℝ) : AddCircle (2 * Real.pi))
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq x
  have hc := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hc
  obtain ⟨M, hM⟩ := hc δ hδ
  have h1 : dist ((x ∘ φ) (M + 1)) ((x ∘ φ) M) < δ := hM (M + 1) (Nat.le_succ M)
  have hlt : φ M < φ (M + 1) := hφ (Nat.lt_succ_self M)
  set i := φ M
  set j := φ (M + 1)
  refine ⟨j - i, by omega, fun k hk => ?_⟩
  have h2 : dist (x j) (x i) < δ := h1
  rw [dist_pi_lt_iff hδ] at h2
  have h3 := h2 ⟨k, hk⟩
  simp only [x, dist_eq_norm, ← AddCircle.coe_sub] at h3
  rw [AddCircle.norm_eq] at h3
  refine ⟨round (((j : ℝ) * T * γ k - (i : ℝ) * T * γ k) / (2 * Real.pi)), ?_⟩
  have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := by
    rw [Nat.cast_sub hlt.le]
  rw [hcast]
  convert h3 using 2
  ring_nf

/-- `1 − cos x ≤ δ² / 2` when `x` is within `δ` of a multiple of `2π`. -/
theorem one_sub_cos_le {x δ : ℝ} {m : ℤ} (h : |x - 2 * Real.pi * m| < δ) :
    1 - Real.cos x ≤ δ ^ 2 / 2 := by
  have hc : Real.cos x = Real.cos (x - 2 * Real.pi * m) := by
    have := Real.cos_sub_int_mul_two_pi x m
    rw [← this]; congr 1; ring
  have h1 := Real.one_sub_sq_div_two_le_cos (x := x - 2 * Real.pi * m)
  have h2 : (x - 2 * Real.pi * m) ^ 2 ≤ δ ^ 2 := by
    have := abs_lt.mp h
    nlinarith [this.1, this.2]
  rw [hc]
  linarith

theorem sum_nonneg' {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) (γ : ℕ → ℝ) (L : ℝ) :
    0 ≤ ∑' k, w k * (1 - Real.cos (γ k * L)) :=
  tsum_nonneg fun k => mul_nonneg (hw k) (by linarith [Real.cos_le_one (γ k * L)])

/-- **F8.** For `w_k ≥ 0` summable and any real `γ_k`: for every `ε > 0` and `T`, there is `L ≥ T`
with `Σ_k w_k (1 − cos γ_k L) < ε`; together with `sum_nonneg'` this is
`liminf_{L → ∞} Σ_k w_k (1 − cos γ_k L) = 0`. -/
theorem dirichlet_liminf {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) (hs : Summable w) (γ : ℕ → ℝ)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    ∃ L : ℝ, T ≤ L ∧ ∑' k, w k * (1 - Real.cos (γ k * L)) < ε := by
  have hW : 0 ≤ ∑' k, w k := tsum_nonneg hw
  -- cut the tail: `2 Σ_{k ≥ N} w_k < ε / 2`
  have htail : Tendsto (fun N => ∑' k, w (k + N)) atTop (𝓝 0) := tendsto_sum_nat_add w
  obtain ⟨N, hN⟩ := (htail.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))).exists
  -- head accuracy `δ` with `δ² / 2 * Σ w ≤ ε / 4`
  set S := ∑' k, w k with hS
  set δ : ℝ := Real.sqrt (ε / (2 * (S + 1))) with hδ
  have hSpos : 0 < S + 1 := by linarith
  have hδ0 : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδ2 : δ ^ 2 = ε / (2 * (S + 1)) := Real.sq_sqrt (by positivity)
  set T' : ℝ := max T 1 with hT'
  have hT'0 : 0 < T' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨j, hj, hret⟩ := simultaneous_return N γ (T := T') hδ0
  refine ⟨(j : ℝ) * T', ?_, ?_⟩
  · have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    calc T ≤ T' := le_max_left _ _
      _ = 1 * T' := (one_mul _).symm
      _ ≤ (j : ℝ) * T' := by nlinarith
  · set L : ℝ := (j : ℝ) * T' with hL
    -- summability of the terms
    have hterm : ∀ k, 0 ≤ w k * (1 - Real.cos (γ k * L)) := fun k =>
      mul_nonneg (hw k) (by linarith [Real.cos_le_one (γ k * L)])
    have hle : ∀ k, w k * (1 - Real.cos (γ k * L)) ≤ 2 * w k := fun k =>
      by nlinarith [hw k, Real.neg_one_le_cos (γ k * L)]
    have hsum : Summable fun k => w k * (1 - Real.cos (γ k * L)) :=
      Summable.of_nonneg_of_le hterm hle (hs.mul_left 2)
    rw [← Summable.sum_add_tsum_nat_add N hsum]
    -- head
    have hhead : ∑ k ∈ Finset.range N, w k * (1 - Real.cos (γ k * L))
        ≤ ∑ k ∈ Finset.range N, w k * (δ ^ 2 / 2) := by
      refine Finset.sum_le_sum fun k hk => ?_
      apply mul_le_mul_of_nonneg_left _ (hw k)
      obtain ⟨m, hm⟩ := hret k (Finset.mem_range.mp hk)
      apply one_sub_cos_le (m := m) (δ := δ)
      have : γ k * L = (j : ℝ) * T' * γ k := by rw [hL]; ring
      rw [this]; exact hm
    have hhead2 : ∑ k ∈ Finset.range N, w k * (δ ^ 2 / 2) ≤ S * (δ ^ 2 / 2) := by
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact hs.sum_le_tsum _ (fun k _ => hw k)
    -- tail
    have htl : ∑' k, w (k + N) * (1 - Real.cos (γ (k + N) * L)) ≤ 2 * ∑' k, w (k + N) := by
      rw [← tsum_mul_left]
      exact Summable.tsum_le_tsum (fun k => hle (k + N))
        ((summable_nat_add_iff N).mpr hsum) ((summable_nat_add_iff N).mpr hs |>.mul_left 2)
    have hd : S * (δ ^ 2 / 2) ≤ ε / 4 := by
      rw [hδ2]
      have : S * (ε / (2 * (S + 1)) / 2) = ε / 4 * (S / (S + 1)) := by
        field_simp; ring
      rw [this]
      have : S / (S + 1) ≤ 1 := by rw [div_le_one hSpos]; linarith
      nlinarith [show (0 : ℝ) < ε / 4 by positivity, show 0 ≤ S / (S + 1) from by positivity]
    linarith

/-- `liminf` form: the quantity is `≥ 0` and is `< ε` at arbitrarily large `L`. -/
theorem dirichlet_liminf_frequently {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) (hs : Summable w)
    (γ : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ L in atTop, ∑' k, w k * (1 - Real.cos (γ k * L)) < ε := by
  rw [Filter.frequently_atTop]
  intro T
  obtain ⟨L, hL, h⟩ := dirichlet_liminf hw hs γ hε T
  exact ⟨L, hL, h⟩

end GppHeartDirichlet

#print axioms GppHeartDirichlet.simultaneous_return
#print axioms GppHeartDirichlet.dirichlet_liminf
#print axioms GppHeartDirichlet.dirichlet_liminf_frequently
