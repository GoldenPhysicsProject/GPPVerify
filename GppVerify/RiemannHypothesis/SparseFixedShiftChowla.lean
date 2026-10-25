import Mathlib.Tactic

/-!
# Fixed-shift correlations vanish, yet the support grows like `X^{2/3}`

Source: Codex, `work/codex/2026-10-21_sparse_fixedshift_chowla_cesaro_energy_obstruction.md`
(GPP-bridge), §2. Daniel Toupin / Golden Physics Project, with AI assistance from Codex
(statement) and Claude Code (formalization).

Codex's countermodel is the 0–1 sequence supported on `s_k = ⌊k^{3/2}⌋`. In `ℕ` this is
`s_k = Nat.sqrt (k³)`.

* `s_strictMono`: `s` is strictly increasing.
* `gap_gt`: for `k ≥ (h+1)²`, `s_{k+1} > s_k + h`, so the support gaps tend to infinity.
* `shift_pair_le`: for every shift `h ≥ 1`, if `n` and `n + h` both lie in the support then
  `n ≤ s_{(h+1)²}`.
* `corr_eventually_const`: hence for every fixed `h ≥ 1` the correlation sum
  `Σ_{n<X} a_n a_{n+h}` is constant for `X > s_{(h+1)²}`. It is `O_h(1)`, not just `o(X)`.
* `mem_support_iff_cube`: `s_k ≤ X ↔ k³ < (X+1)²`.
* `count_ge`, `count_le`: for the counting function `A(X) = #{k ≥ 1 : s_k ≤ X}`,
  `m³ < (X+1)² ⇒ m ≤ A(X)` and `(X+1)² ≤ (m+1)³ ⇒ A(X) ≤ m`. So `A(X)` is the integer cube
  root of `(X+1)²` up to the boundary, i.e. `A(X) = X^{2/3} + O(1)`.

The point, as in the note, is that every fixed-shift correlation is eventually silent while the
support still grows like a positive power. So fixed-`h` Chowla-type input cannot control the
Cesàro energy `E_N = ∫₁^N A(x)²/x² dx ~ 3N^{1/3}`. That needs shifts `h ~ N`.

**Scope.** The real-analytic step `A(X) = X^{2/3} + O(1)` and the energy asymptotic
`E_N = 3N^{1/3} + O(1)` are not formalized; only the integer sandwich is. The sequence is not
multiplicative, so this is a logical obstruction, not an arithmetic counterexample. The note's
audit of the September 2026 two-point-correlation preprint is not checked. No claim about RH.
-/

set_option autoImplicit false

open Finset

namespace GppSparseChowla

/-- `s_k = ⌊k^{3/2}⌋ = Nat.sqrt (k³)`. -/
def s (k : ℕ) : ℕ := Nat.sqrt (k ^ 3)

lemma s_sq_le (k : ℕ) : s k ^ 2 ≤ k ^ 3 := by
  rw [s]; exact Nat.sqrt_le' _

/-- Key gap lemma: for `k ≥ (h+1)²`, `s_{k+1} ≥ s_k + h + 1`. -/
theorem gap_gt {h k : ℕ} (hk : (h + 1) ^ 2 ≤ k) : s k + h < s (k + 1) := by
  have hr := s_sq_le k
  set r := s k
  -- `2(h+1) r ≤ 3k²` via squares
  have h1 : (2 * (h + 1) * r) ^ 2 ≤ (3 * k ^ 2) ^ 2 := by
    have : (2 * (h + 1) * r) ^ 2 = 4 * (h + 1) ^ 2 * r ^ 2 := by ring
    rw [this]
    calc 4 * (h + 1) ^ 2 * r ^ 2 ≤ 4 * k * k ^ 3 := by gcongr
      _ ≤ (3 * k ^ 2) ^ 2 := by nlinarith
  have h2 : 2 * (h + 1) * r ≤ 3 * k ^ 2 := by
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
  have hsq : (r + h + 1) * (r + h + 1) ≤ (k + 1) ^ 3 := by nlinarith
  have := Nat.le_sqrt.mpr hsq
  rw [s]; omega

theorem s_strictMono : StrictMono s := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · decide
  · have hr := s_sq_le k
    have hr2 : s k ≤ k ^ 2 := by
      have : s k ^ 2 ≤ (k ^ 2) ^ 2 := by
        calc s k ^ 2 ≤ k ^ 3 := hr
          _ ≤ (k ^ 2) ^ 2 := by rw [← pow_mul]; exact Nat.pow_le_pow_right hk (by norm_num)
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
    have hsq : (s k + 1) * (s k + 1) ≤ (k + 1) ^ 3 := by nlinarith
    exact Nat.lt_of_succ_le (Nat.le_sqrt.mpr hsq)

/-- The support `{s_k : k ≥ 1}`. -/
def InSupp (n : ℕ) : Prop := ∃ k, 1 ≤ k ∧ s k = n

/-- **Fixed shifts see only finitely many pairs.** -/
theorem shift_pair_le {h n : ℕ} (hh : 1 ≤ h) (hn : InSupp n) (hnh : InSupp (n + h)) :
    n ≤ s ((h + 1) ^ 2) := by
  obtain ⟨i, -, rfl⟩ := hn
  obtain ⟨j, -, hj⟩ := hnh
  have hij : i < j := s_strictMono.lt_iff_lt.mp (by omega)
  by_contra hc
  push Not at hc
  have hi : (h + 1) ^ 2 ≤ i := by
    by_contra hi; push Not at hi
    exact absurd (s_strictMono.monotone hi.le) (by omega)
  have hg := gap_gt hi
  have hmono : s (i + 1) ≤ s j := s_strictMono.monotone hij
  omega

open Classical in
/-- The indicator `a_n = 1` on the support, `0` off it. -/
noncomputable def a (n : ℕ) : ℕ := if InSupp n then 1 else 0

/-- **Every fixed-shift correlation is eventually constant.** -/
theorem corr_eventually_const {h : ℕ} (hh : 1 ≤ h) {X : ℕ} (hX : s ((h + 1) ^ 2) < X) :
    ∑ n ∈ range X, a n * a (n + h) = ∑ n ∈ range (s ((h + 1) ^ 2) + 1), a n * a (n + h) := by
  have hsplit := sum_range_add_sum_Ico (fun n => a n * a (n + h)) (Nat.succ_le_of_lt hX)
  rw [← hsplit, add_eq_left]
  refine sum_eq_zero fun n hn => ?_
  have hn' := (mem_Ico.mp hn).1
  unfold a
  by_cases h1 : InSupp n
  · by_cases h2 : InSupp (n + h)
    · exact absurd (shift_pair_le hh h1 h2) (by omega)
    · simp [h2]
  · simp [h1]

/-- `s_k ≤ X ↔ k³ < (X+1)²`. -/
theorem mem_support_iff_cube (k X : ℕ) : s k ≤ X ↔ k ^ 3 < (X + 1) ^ 2 := by
  rw [s, ← Nat.lt_succ_iff, Nat.sqrt_lt', sq]

/-- The counting function `A(X) = #{k ≥ 1 : s_k ≤ X}` (all such `k` are `≤ X + 1`). -/
def A (X : ℕ) : ℕ := ((Icc 1 (X + 1)).filter fun k => s k ≤ X).card

lemma k_le_of_cube {k X : ℕ} (h : k ^ 3 < (X + 1) ^ 2) : k ≤ X + 1 := by
  by_contra hc; push Not at hc
  have : (X + 1) ^ 2 < k ^ 3 := by
    calc (X + 1) ^ 2 < k ^ 2 := Nat.pow_lt_pow_left hc (by norm_num)
      _ ≤ k ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

/-- Lower half of the sandwich: `m³ < (X+1)² ⇒ m ≤ A(X)`. -/
theorem count_ge {m X : ℕ} (hm : m ^ 3 < (X + 1) ^ 2) : m ≤ A X := by
  have hsub : Icc 1 m ⊆ (Icc 1 (X + 1)).filter fun k => s k ≤ X := by
    intro k hk
    rw [mem_Icc] at hk
    have hk3 : k ^ 3 < (X + 1) ^ 2 :=
      lt_of_le_of_lt (Nat.pow_le_pow_left hk.2 3) hm
    rw [mem_filter, mem_Icc, mem_support_iff_cube]
    exact ⟨⟨hk.1, k_le_of_cube hk3⟩, hk3⟩
  have := card_le_card hsub
  rw [Nat.card_Icc] at this
  unfold A; omega

/-- Upper half of the sandwich: `(X+1)² ≤ (m+1)³ ⇒ A(X) ≤ m`. -/
theorem count_le {m X : ℕ} (hm : (X + 1) ^ 2 ≤ (m + 1) ^ 3) : A X ≤ m := by
  have hsub : ((Icc 1 (X + 1)).filter fun k => s k ≤ X) ⊆ Icc 1 m := by
    intro k hk
    rw [mem_filter, mem_Icc, mem_support_iff_cube] at hk
    rw [mem_Icc]
    refine ⟨hk.1.1, ?_⟩
    by_contra hc; push Not at hc
    have : (m + 1) ^ 3 ≤ k ^ 3 := Nat.pow_le_pow_left hc 3
    omega
  have := card_le_card hsub
  rw [Nat.card_Icc] at this
  unfold A; omega

end GppSparseChowla
