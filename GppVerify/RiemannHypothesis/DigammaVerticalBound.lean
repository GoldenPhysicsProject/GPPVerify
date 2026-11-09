/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.DigammaGaussSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Explicit formula, stage E2b: the digamma function on vertical strips

For `|Re s| ≤ M` and `|Im s| ≥ 1`,

  `‖ψ(s)‖ ≤ C · log (|Im s| + 1)`   (`norm_digamma_le`),

with `C` depending only on `M`. Proof from Gauss's series (E2a): each term is
`s / ((n+1)(n+1+s))`, bounded by `4 (M+1) L / ((n+1)(n+1+L))` once `n + 1 ≥ 2M`
(`L = |Im s|`), and by `M + 1` for the finitely many smaller `n`; the first family sums to
`O(log L)` (`sum_range_le_log`, harmonic bound plus the tail `∑ 1/m² ≤ 2/(K+1)`).

Stage E2b of the explicit-formula plan (bridge
`MuseResearch/claude-code-note-2026-11-07-explicit-formula-plan.md`). No claim about RH.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.
-/

open Finset

namespace GppDigammaVertical


/-- Elementary bound: `∑_{i<n} L / ((i+1)(i+1+L)) ≤ 3 + log (L+1)` for `L ≥ 1`. -/
theorem sum_range_le_log (L : ℝ) (hL : 1 ≤ L) (n : ℕ) :
    ∑ i ∈ range n, L / (((i : ℝ) + 1) * ((i : ℝ) + 1 + L)) ≤ 3 + Real.log (L + 1) := by
  set K := ⌈L⌉₊ with hK
  have hKL : L ≤ K := Nat.le_ceil L
  have hKL' : (K : ℝ) < L + 1 := Nat.ceil_lt_add_one (by linarith)
  have hK1 : 1 ≤ K := Nat.one_le_ceil_iff.2 (by linarith)
  have hpt : ∀ i ∈ range n, L / (((i : ℝ) + 1) * ((i : ℝ) + 1 + L)) ≤
      (if i < K then (1 / ((i : ℝ) + 1)) else 0) +
      (if K ≤ i then L * ((((i + 1 : ℕ) : ℝ)) ^ 2)⁻¹ else 0) := by
    intro i _
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hiL : (0 : ℝ) < (i : ℝ) + 1 + L := by linarith
    by_cases h : i < K
    · rw [if_pos h, if_neg (by omega), add_zero]
      rw [div_le_div_iff₀ (mul_pos hi hiL) hi]
      nlinarith
    · rw [if_neg h, if_pos (by omega), zero_add]
      push_cast
      rw [← div_eq_mul_inv, div_le_div_iff₀ (mul_pos hi hiL) (by positivity)]
      have hL0 : (0 : ℝ) < L := by linarith
      nlinarith [mul_pos (mul_pos hL0 hi) hL0]
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib]
  have h1 : ∑ i ∈ range n, (if i < K then (1 / ((i : ℝ) + 1)) else 0) ≤ 1 + Real.log (L + 1) := by
    calc ∑ i ∈ range n, (if i < K then (1 / ((i : ℝ) + 1)) else 0)
        ≤ ∑ i ∈ range K, (1 / ((i : ℝ) + 1)) := by
          rw [← sum_filter]
          refine sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
          intro i hi
          simp only [mem_filter, mem_range] at hi
          exact mem_range.2 hi.2
      _ = (harmonic K : ℝ) := by
          simp [harmonic, one_div]
      _ ≤ 1 + Real.log K := harmonic_le_one_add_log K
      _ ≤ 1 + Real.log (L + 1) := by
          have : Real.log K ≤ Real.log (L + 1) :=
            Real.log_le_log (by exact_mod_cast (show 0 < K by omega)) hKL'.le
          linarith
  have h2 : ∑ i ∈ range n, (if K ≤ i then L * ((((i + 1 : ℕ) : ℝ)) ^ 2)⁻¹ else 0) ≤ 2 := by
    set F : ℕ → ℝ := fun m => if K < m then L * ((m : ℝ) ^ 2)⁻¹ else 0 with hF
    have e1 : ∑ i ∈ range n, (if K ≤ i then L * ((((i + 1 : ℕ) : ℝ)) ^ 2)⁻¹ else 0) =
        ∑ i ∈ range n, F (i + 1) := by
      refine sum_congr rfl fun i _ => ?_
      simp only [hF]
      by_cases h : K ≤ i
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    have e2 : ∑ i ∈ range n, F (i + 1) = ∑ m ∈ range (n + 1), F m := by
      rw [sum_range_succ' F n]
      simp [hF]
    have e3 : ∑ m ∈ range (n + 1), F m = L * ∑ m ∈ Ioo K (n + 1), ((m : ℝ) ^ 2)⁻¹ := by
      simp only [hF]
      rw [← sum_filter, mul_sum]
      refine sum_congr ?_ (fun _ _ => rfl)
      ext m; simp only [mem_filter, mem_range, mem_Ioo]; omega
    rw [e1, e2, e3]
    have h4 := sum_Ioo_inv_sq_le (α := ℝ) K (n + 1)
    have hL0 : (0 : ℝ) < L := by linarith
    calc L * ∑ m ∈ Ioo K (n + 1), ((m : ℝ) ^ 2)⁻¹ ≤ L * (2 / ((K : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h4 hL0.le
      _ ≤ 2 := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  linarith

open GppDigammaSeries Complex in
/-- Termwise bound for the Gauss series. -/
theorem norm_term_le (M L : ℝ) (hM : 0 ≤ M) (s : ℂ) (hre : |s.re| ≤ M) (hL : L = |s.im|)
    (h1 : 1 ≤ L) (n : ℕ) :
    ‖digammaSeriesTerm s n‖ ≤
      (M + 1) * (if (n : ℝ) + 1 < 2 * M then 1 else 0) +
        4 * (M + 1) * (L / (((n : ℝ) + 1) * ((n : ℝ) + 1 + L))) := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpole : (n : ℂ) + 1 + s ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    have : s.im = 0 := by linarith
    rw [this] at hL; simp at hL; linarith
  rw [digammaSeriesTerm_eq hpole, norm_div, norm_mul]
  have hnorm1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_of_nonneg hN.le]
  rw [hnorm1]
  have hK : ‖s‖ ≤ (M + 1) * L := by
    have h2 : ‖s‖ ≤ |s.re| + |s.im| := by
      simpa [Real.sqrt_le_sqrt] using Complex.norm_le_abs_re_add_abs_im s
    nlinarith
  have hLle : L ≤ ‖(n : ℂ) + 1 + s‖ := by
    rw [hL]
    have := Complex.abs_im_le_norm ((n : ℂ) + 1 + s)
    simpa using this
  have hre' : (n : ℝ) + 1 + s.re ≤ ‖(n : ℂ) + 1 + s‖ := by
    have := Complex.re_le_norm ((n : ℂ) + 1 + s)
    simpa using this
  have hnn : 0 ≤ ‖s‖ := norm_nonneg _
  by_cases hsmall : (n : ℝ) + 1 < 2 * M
  · rw [if_pos hsmall]
    have hpos : 0 < ‖(n : ℂ) + 1 + s‖ := by linarith
    have hterm : ‖s‖ / (((n : ℝ) + 1) * ‖(n : ℂ) + 1 + s‖) ≤ M + 1 := by
      rw [div_le_iff₀ (mul_pos hN hpos)]
      have : (M + 1) * L ≤ (M + 1) * (((n : ℝ) + 1) * ‖(n : ℂ) + 1 + s‖) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        nlinarith
      linarith
    have hpart : 0 ≤ 4 * (M + 1) * (L / (((n : ℝ) + 1) * ((n : ℝ) + 1 + L))) := by positivity
    linarith
  · rw [if_neg hsmall]
    push Not at hsmall
    have hge : ((n : ℝ) + 1) / 2 ≤ ‖(n : ℂ) + 1 + s‖ := by
      have := neg_abs_le s.re
      have := abs_le.1 hre
      linarith
    have hge' : ((n : ℝ) + 1 + L) / 4 ≤ ‖(n : ℂ) + 1 + s‖ := by linarith
    have hpos : 0 < ‖(n : ℂ) + 1 + s‖ := by linarith
    rw [mul_zero, zero_add, div_le_iff₀ (mul_pos hN hpos)]
    have hc : 0 ≤ 4 * (M + 1) * (L / (((n : ℝ) + 1) * ((n : ℝ) + 1 + L))) := by positivity
    have e : 4 * (M + 1) * (L / (((n : ℝ) + 1) * ((n : ℝ) + 1 + L))) *
        (((n : ℝ) + 1) * (((n : ℝ) + 1 + L) / 4)) = (M + 1) * L := by
      have h1 : (n : ℝ) + 1 + L ≠ 0 := by linarith
      field_simp
    calc ‖s‖ ≤ (M + 1) * L := hK
      _ = 4 * (M + 1) * (L / (((n : ℝ) + 1) * ((n : ℝ) + 1 + L))) *
            (((n : ℝ) + 1) * (((n : ℝ) + 1 + L) / 4)) := e.symm
      _ ≤ 4 * (M + 1) * (L / (((n : ℝ) + 1) * ((n : ℝ) + 1 + L))) *
            (((n : ℝ) + 1) * ‖(n : ℂ) + 1 + s‖) := by
          apply mul_le_mul_of_nonneg_left _ hc
          exact mul_le_mul_of_nonneg_left hge' hN.le

open GppDigammaSeries GppDigammaGaussSeries Complex in
/-- **`ψ(s) = O(log |Im s|)` on vertical strips.** -/
theorem norm_digamma_le (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, ∀ s : ℂ, |s.re| ≤ M → 1 ≤ |s.im| →
      ‖Complex.digamma s‖ ≤ C * Real.log (|s.im| + 1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set A : ℝ := |Real.eulerMascheroniConstant| + 1 + (M + 1) * (2 * M + 1) + 12 * (M + 1) with hA
  refine ⟨A / Real.log 2 + 4 * (M + 1), fun s hre him => ?_⟩
  set L : ℝ := |s.im| with hL
  have hs : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.im h
    simp at this
    rw [hL, this] at him; simp at him; linarith
  rw [← digammaSeries_eq_digamma hs]
  -- bounds on the series
  set f1 : ℕ → ℝ := fun n => (M + 1) * (if (n : ℝ) + 1 < 2 * M then 1 else 0) with hf1
  set f2 : ℕ → ℝ := fun n => 4 * (M + 1) * (L / (((n : ℝ) + 1) * ((n : ℝ) + 1 + L))) with hf2
  have hf1nn : ∀ n, 0 ≤ f1 n := fun n => by simp only [hf1]; split_ifs <;> positivity
  have hf2nn : ∀ n, 0 ≤ f2 n := fun n => by simp only [hf2]; have : (1:ℝ) ≤ L := him; positivity
  have hP1 : ∀ n, ∑ i ∈ range n, f1 i ≤ (M + 1) * (2 * M + 1) := by
    intro n
    simp only [hf1]
    rw [← mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    calc ∑ i ∈ range n, (if (i : ℝ) + 1 < 2 * M then (1 : ℝ) else 0)
        ≤ ∑ i ∈ range ⌈2 * M⌉₊, (1 : ℝ) := by
          rw [← sum_filter]
          refine (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => zero_le_one)).trans' le_rfl
          intro i hi
          simp only [mem_filter, mem_range] at hi
          rw [mem_range]
          have : (i : ℝ) < ⌈2 * M⌉₊ := by
            have := Nat.le_ceil (2 * M)
            linarith [hi.2]
          exact_mod_cast this
      _ = (⌈2 * M⌉₊ : ℝ) := by simp
      _ ≤ 2 * M + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hP2 : ∀ n, ∑ i ∈ range n, f2 i ≤ 4 * (M + 1) * (3 + Real.log (L + 1)) := by
    intro n
    simp only [hf2]
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_range_le_log L him n) (by positivity)
  have hS1 : Summable f1 := summable_of_sum_range_le hf1nn hP1
  have hS2 : Summable f2 := summable_of_sum_range_le hf2nn hP2
  have hT1 : ∑' n, f1 n ≤ (M + 1) * (2 * M + 1) := Real.tsum_le_of_sum_range_le hf1nn hP1
  have hT2 : ∑' n, f2 n ≤ 4 * (M + 1) * (3 + Real.log (L + 1)) :=
    Real.tsum_le_of_sum_range_le hf2nn hP2
  have hterm : ∀ n, ‖digammaSeriesTerm s n‖ ≤ f1 n + f2 n :=
    fun n => norm_term_le M L hM s hre hL him n
  have hSn : Summable (fun n => ‖digammaSeriesTerm s n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hS1.add hS2)
  have htsum : ‖∑' n, digammaSeriesTerm s n‖ ≤ ∑' n, (f1 n + f2 n) :=
    (norm_tsum_le_tsum_norm hSn).trans (hSn.tsum_le_tsum hterm (hS1.add hS2))
  rw [hS1.tsum_add hS2] at htsum
  have hsinv : ‖s⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have : (1 : ℝ) ≤ ‖s‖ := him.trans (by simpa using Complex.abs_im_le_norm s)
    exact inv_le_one_of_one_le₀ this
  have hγ : ‖(Real.eulerMascheroniConstant : ℂ)‖ = |Real.eulerMascheroniConstant| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hlogL : Real.log 2 ≤ Real.log (L + 1) := Real.log_le_log (by norm_num) (by linarith)
  unfold digammaSeries
  calc ‖-(Real.eulerMascheroniConstant : ℂ) - s⁻¹ + ∑' n, digammaSeriesTerm s n‖
      ≤ ‖-(Real.eulerMascheroniConstant : ℂ)‖ + ‖s⁻¹‖ + ‖∑' n, digammaSeriesTerm s n‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ |Real.eulerMascheroniConstant| + 1 + ((M + 1) * (2 * M + 1) +
          4 * (M + 1) * (3 + Real.log (L + 1))) := by
        rw [norm_neg, hγ]; linarith
    _ ≤ (A / Real.log 2 + 4 * (M + 1)) * Real.log (L + 1) := by
        have h1 : A ≤ A / Real.log 2 * Real.log (L + 1) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
          have hAnn : 0 ≤ A := by simp only [hA]; positivity
          nlinarith
        nlinarith [mul_nonneg (by linarith : 0 ≤ M + 1) (Real.log_nonneg (by linarith : (1:ℝ) ≤ L + 1))]

end GppDigammaVertical
