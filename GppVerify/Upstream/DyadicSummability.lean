/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Set.Finite.Basic

/-!
# Summability from a polynomial counting bound

Let `a : ι → ℝ` be a family of positive reals for which every "ball" `{i | a i ≤ r}` is finite,
with a polynomial bound on its size:

  `#{i | a i ≤ r} ≤ A + B * r ^ ρ`.

Then `∑ i, (a i) ^ (-s)` converges for every `s > ρ`.

This is the dyadic half of the passage from Jensen's zero-counting inequality to the
hypothesis of the Weierstrass product. `Complex.HasOrderLE.sum_divisor_le` supplies the
counting bound `n(r) ≤ A + B r ^ (ρ + ε)` for an entire function of order at most `ρ`;
`Complex.weierstrassProduct` consumes `Summable fun n => ‖a n‖⁻¹ ^ (p + 1)`. This file is
the step between them, and it is the step that was named as missing.

## The argument

Cut the index set into dyadic shells. Write `T k = {i | a i ≤ 2 ^ k}`, a finite set. Every
`i` lies in some `T k`, the `T k` increase, and on the shell `T (k+1) \ T k` we have
`2 ^ k < a i`, hence `a i ^ (-s) ≤ 2 ^ (-k s)`. The shell has at most
`#T (k+1) ≤ A + B 2 ^ ((k+1) ρ)` elements, so it contributes at most

  `(A + B 2 ^ ((k+1) ρ)) * 2 ^ (-k s) = A (2 ^ (-s)) ^ k + B 2 ^ ρ (2 ^ (ρ - s)) ^ k`.

Both are geometric with ratio `< 1`, because `s > 0` and `ρ - s < 0`. So the partial sums over
every finite subset are bounded by one constant, and `summable_of_sum_le` finishes.

Two details that are easy to get wrong and are handled explicitly below.

* `A` need not be nonnegative. Jensen produces `A = (log (C+1) - log ‖f 0‖) / log 2`, which is
  negative whenever `‖f 0‖ > C + 1`. Multiplying a bound through by a geometric series
  reverses the inequality for a negative coefficient, so the proof runs with `max A 0`
  throughout. This is free: `A + B r ^ ρ ≤ max A 0 + B r ^ ρ`.
* The hypothesis is only ever used at `r = 2 ^ k`, so nothing is assumed about small `r`.

## Main results

* `Real.summable_rpow_neg_of_counting_le` : the statement above, for real exponents.
* `Real.summable_inv_pow_of_counting_le` : the same with a natural exponent `m > ρ`, in the
  shape `Summable fun i => (a i)⁻¹ ^ m` that `Complex.weierstrassProduct` takes.
-/

open Finset Set

namespace Real

variable {ι : Type*}

/-- **A polynomial bound on the counting function forces `∑ (a i) ^ (-s)` to converge for
every `s` beyond the growth exponent.**

If the family of positive reals `a` has `#{i | a i ≤ r} ≤ A + B r ^ ρ` for all `r > 0`, then
`fun i => a i ^ (-s)` is summable whenever `ρ < s`. -/
theorem summable_rpow_neg_of_counting_le {a : ι → ℝ} (hpos : ∀ i, 0 < a i)
    (hfin : ∀ r : ℝ, {i | a i ≤ r}.Finite) {A B ρ s : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hs : ρ < s)
    (hcount : ∀ r : ℝ, 0 < r → (((hfin r).toFinset.card : ℕ) : ℝ) ≤ A + B * r ^ ρ) :
    Summable fun i => a i ^ (-s) := by
  classical
  have hspos : 0 < s := lt_of_le_of_lt hρ hs
  set A' : ℝ := max A 0 with hA'def
  have hA' : 0 ≤ A' := le_max_right _ _
  have hAA' : A ≤ A' := le_max_left _ _
  -- the dyadic balls
  set T : ℕ → Finset ι := fun k => (hfin ((2 : ℝ) ^ k)).toFinset with hTdef
  have hmemT : ∀ (k : ℕ) (i : ι), i ∈ T k ↔ a i ≤ (2 : ℝ) ^ k := by
    intro k i; simp [hTdef, Set.Finite.mem_toFinset]
  have htwo : (1 : ℝ) < 2 := one_lt_two
  have htwok : ∀ k : ℕ, (0 : ℝ) < (2 : ℝ) ^ k := fun k => by positivity
  have hsubT : ∀ k : ℕ, T k ⊆ T (k + 1) := by
    intro k i hi
    rw [hmemT] at hi ⊢
    exact hi.trans (pow_le_pow_right₀ htwo.le (Nat.le_succ k))
  -- the nonnegative summand
  have hfnn : ∀ i, 0 ≤ a i ^ (-s) := fun i => (Real.rpow_pos_of_pos (hpos i) _).le
  -- rewrite `2 ^ k` as an rpow so the counting bound composes with `rpow_mul`
  have hpow_rpow : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ ρ = ((2 : ℝ) ^ ρ) ^ k := by
    intro k
    rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  -- the card bound, with a nonnegative constant term
  have hcardT : ∀ k : ℕ, ((T k).card : ℝ) ≤ A' + B * ((2 : ℝ) ^ ρ) ^ k := by
    intro k
    have := hcount ((2 : ℝ) ^ k) (htwok k)
    rw [hpow_rpow k] at this
    exact this.trans (by nlinarith)
  -- the two geometric ratios
  set q₁ : ℝ := (2 : ℝ) ^ (-s) with hq₁def
  set q₂ : ℝ := (2 : ℝ) ^ (ρ - s) with hq₂def
  have hq₁nn : 0 ≤ q₁ := Real.rpow_nonneg (by norm_num) _
  have hq₂nn : 0 ≤ q₂ := Real.rpow_nonneg (by norm_num) _
  have hq₁lt : q₁ < 1 := by
    have : (2 : ℝ) ^ (-s) < (2 : ℝ) ^ (0 : ℝ) :=
      (Real.rpow_lt_rpow_left_iff htwo).2 (by linarith)
    simpa [hq₁def] using this
  have hq₂lt : q₂ < 1 := by
    have : (2 : ℝ) ^ (ρ - s) < (2 : ℝ) ^ (0 : ℝ) :=
      (Real.rpow_lt_rpow_left_iff htwo).2 (by linarith)
    simpa [hq₂def] using this
  -- each shell's contribution
  have hshell : ∀ k : ℕ,
      ∑ i ∈ T (k + 1) \ T k, a i ^ (-s) ≤ A' * q₁ ^ k + (B * (2 : ℝ) ^ ρ) * q₂ ^ k := by
    intro k
    have hbd : ∀ i ∈ T (k + 1) \ T k, a i ^ (-s) ≤ q₁ ^ k := by
      intro i hi
      rw [Finset.mem_sdiff, hmemT, hmemT] at hi
      have hlt : (2 : ℝ) ^ k < a i := lt_of_not_ge hi.2
      have h1 : ((2 : ℝ) ^ k) ^ s ≤ (a i) ^ s :=
        Real.rpow_le_rpow (htwok k).le hlt.le hspos.le
      have h2 : (a i) ^ (-s) ≤ ((2 : ℝ) ^ k) ^ (-s) := by
        rw [Real.rpow_neg (hpos i).le, Real.rpow_neg (htwok k).le]
        exact inv_anti₀ (Real.rpow_pos_of_pos (htwok k) _) h1
      refine h2.trans_eq ?_
      rw [hq₁def, ← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_natCast ((2 : ℝ) ^ (-s)) k,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
      ring_nf
    calc ∑ i ∈ T (k + 1) \ T k, a i ^ (-s)
        ≤ (T (k + 1) \ T k).card • q₁ ^ k :=
          Finset.sum_le_card_nsmul _ _ _ hbd
      _ = ((T (k + 1) \ T k).card : ℝ) * q₁ ^ k := by simp [nsmul_eq_mul]
      _ ≤ ((T (k + 1)).card : ℝ) * q₁ ^ k := by
          have : ((T (k + 1) \ T k).card : ℝ) ≤ ((T (k + 1)).card : ℝ) := by
            exact_mod_cast Nat.cast_le.2 (Finset.card_le_card (Finset.sdiff_subset))
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ (A' + B * ((2 : ℝ) ^ ρ) ^ (k + 1)) * q₁ ^ k :=
          mul_le_mul_of_nonneg_right (hcardT (k + 1)) (by positivity)
      _ = A' * q₁ ^ k + (B * (2 : ℝ) ^ ρ) * q₂ ^ k := by
          have hq : q₂ ^ k = ((2 : ℝ) ^ ρ) ^ k * q₁ ^ k := by
            rw [hq₂def, hq₁def, ← mul_pow, ← Real.rpow_add (by norm_num)]
            ring_nf
          rw [hq]; ring
  -- the partial sums over the dyadic balls, by induction on the level
  have hTK : ∀ K : ℕ, ∑ i ∈ T K, a i ^ (-s)
      ≤ (∑ i ∈ T 0, a i ^ (-s)) + ∑ k ∈ range K, (A' * q₁ ^ k + (B * (2 : ℝ) ^ ρ) * q₂ ^ k) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
        have hsplit : ∑ i ∈ T (K + 1) \ T K, a i ^ (-s) + ∑ i ∈ T K, a i ^ (-s)
            = ∑ i ∈ T (K + 1), a i ^ (-s) := Finset.sum_sdiff (hsubT K)
        rw [Finset.sum_range_succ, ← hsplit]
        have := hshell K
        linarith
  -- the geometric majorants
  have hgeo₁ : ∀ K : ℕ, ∑ k ∈ range K, q₁ ^ k ≤ (1 - q₁)⁻¹ := by
    intro K
    have hsum := summable_geometric_of_lt_one hq₁nn hq₁lt
    have := hsum.sum_le_tsum (range K) (fun i _ => by positivity)
    rwa [tsum_geometric_of_lt_one hq₁nn hq₁lt] at this
  have hgeo₂ : ∀ K : ℕ, ∑ k ∈ range K, q₂ ^ k ≤ (1 - q₂)⁻¹ := by
    intro K
    have hsum := summable_geometric_of_lt_one hq₂nn hq₂lt
    have := hsum.sum_le_tsum (range K) (fun i _ => by positivity)
    rwa [tsum_geometric_of_lt_one hq₂nn hq₂lt] at this
  -- every finite subset sits inside some dyadic ball
  have hcover : ∀ u : Finset ι, ∃ K : ℕ, u ⊆ T K := by
    intro u
    induction u using Finset.induction with
    | empty => exact ⟨0, by simp⟩
    | insert x u hx ih =>
        obtain ⟨K, hK⟩ := ih
        obtain ⟨n, hn⟩ := exists_nat_gt (a x)
        have hxle : a x ≤ (2 : ℝ) ^ n := by
          have : (n : ℝ) ≤ (2 : ℝ) ^ n := by
            exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
          linarith
        refine ⟨max K n, ?_⟩
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hiu
        · rw [hmemT]
          refine hxle.trans ?_
          exact pow_le_pow_right₀ htwo.le (le_max_right K n)
        · have : i ∈ T K := hK hiu
          rw [hmemT] at this ⊢
          refine this.trans ?_
          exact pow_le_pow_right₀ htwo.le (le_max_left K n)
  -- assemble. `summable_of_sum_le` cannot infer the bound from the calc block that
  -- establishes it, so name it.
  set C : ℝ := (∑ i ∈ T 0, a i ^ (-s))
      + (A' * (1 - q₁)⁻¹ + (B * (2 : ℝ) ^ ρ) * (1 - q₂)⁻¹) with hCdef
  refine summable_of_sum_le (c := C) hfnn (fun u => ?_)
  obtain ⟨K, hK⟩ := hcover u
  calc ∑ i ∈ u, a i ^ (-s)
      ≤ ∑ i ∈ T K, a i ^ (-s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hK (fun i _ _ => hfnn i)
    _ ≤ (∑ i ∈ T 0, a i ^ (-s))
          + ∑ k ∈ range K, (A' * q₁ ^ k + (B * (2 : ℝ) ^ ρ) * q₂ ^ k) := hTK K
    _ ≤ C := by
        rw [hCdef]
        have hB2 : 0 ≤ B * (2 : ℝ) ^ ρ := by positivity
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have h1 : A' * ∑ k ∈ range K, q₁ ^ k ≤ A' * (1 - q₁)⁻¹ :=
          mul_le_mul_of_nonneg_left (hgeo₁ K) hA'
        have h2 : (B * (2 : ℝ) ^ ρ) * ∑ k ∈ range K, q₂ ^ k
            ≤ (B * (2 : ℝ) ^ ρ) * (1 - q₂)⁻¹ :=
          mul_le_mul_of_nonneg_left (hgeo₂ K) hB2
        linarith

/-- The counting bound in the shape `Complex.weierstrassProduct` consumes: a natural exponent
`m` strictly beyond the growth exponent `ρ` gives `Summable fun i => (a i)⁻¹ ^ m`. -/
theorem summable_inv_pow_of_counting_le {a : ι → ℝ} (hpos : ∀ i, 0 < a i)
    (hfin : ∀ r : ℝ, {i | a i ≤ r}.Finite) {A B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ) {m : ℕ}
    (hm : ρ < m)
    (hcount : ∀ r : ℝ, 0 < r → (((hfin r).toFinset.card : ℕ) : ℝ) ≤ A + B * r ^ ρ) :
    Summable fun i => (a i)⁻¹ ^ m := by
  have h := summable_rpow_neg_of_counting_le hpos hfin hB hρ hm hcount
  refine h.congr (fun i => ?_)
  rw [Real.rpow_neg (hpos i).le, Real.rpow_natCast, ← inv_pow]

end Real
