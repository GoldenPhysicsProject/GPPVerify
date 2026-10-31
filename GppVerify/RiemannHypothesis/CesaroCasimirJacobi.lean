import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The Cesàro Gram operator and the discrete Casimir Jacobi form

Source: Codex / Discovery2, `research/2026-09-20_cesaro_discrete_casimir_principal_series.md`
(`GPPDiscovery2`, `codex/discovery-workbench`), §§1–3. Daniel Toupin / Golden Physics Project, with
AI assistance from Codex (statements) and Claude Code (formalization).

On sequences indexed by `n = 1, 2, …` let `(Cx)_n = (1/n) Σ_{k=1}^{n} x_k` (Cesàro mean) and
`(Dh)_n = n h_n − (n − 1) h_{n−1}`.

* `cesaro_gram_entry`: `(C Cᵀ)_{mn} = Σ_k C_{mk} C_{nk} = 1/max(m,n)`, the reciprocal-Brownian
  kernel.
* `D_cesaro`: `D (C x) = x`.
* `sum_D_sq`: for every `N`, `Σ_{n=1}^{N} (Dh)_n² = Σ_{n=1}^{N−1} n(n+1)(h_n − h_{n+1})² + N h_N²`,
  hence for `h` vanishing from `N` on, `‖Dh‖² = Σ n(n+1)(h_n − h_{n+1})²` (the discrete Casimir
  energy `⟨h, L h⟩`, `L = DᵀD`).
* `hardy_floor`: for finitely supported `h`, `(1/4) Σ h_n² ≤ Σ n(n+1)(h_n − h_{n+1})²` — the
  `1/4` spectral floor `L ≥ ¼ I`, equivalently `‖C‖ ≤ 2` (Hardy).

**Scope.** Finite algebraic identities and the one-sided `1/4` floor for finitely supported
sequences. The sharpness of `1/4`, the identification with Stampach's Hilbert `L`-matrix, the exact
spectrum `σ(L) = [1/4, ∞)` and everything in §§4–6 of the note are not formalized. No claim about RH.
-/

set_option autoImplicit false

open Finset

namespace GppCesaroCasimir

/-- Matrix entry of the Cesàro operator: `C_{nk} = 1/n` for `k ≤ n`, else `0`. -/
noncomputable def cEntry (n k : ℕ) : ℝ := if k ≤ n then 1 / (n : ℝ) else 0

/-- `(C C^T)_{mn} = 1 / max(m, n)` for `m, n ≥ 1`. -/
theorem cesaro_gram_entry (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 (m + n), cEntry m k * cEntry n k = 1 / (max m n : ℕ) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hsum : ∑ k ∈ Icc 1 (m + n), cEntry m k * cEntry n k =
      ∑ k ∈ Icc 1 (min m n), 1 / ((m : ℝ) * n) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 (m + n)) (fun k => k ≤ min m n)]
    have h1 : (Finset.filter (fun k => k ≤ min m n) (Icc 1 (m + n))) = Icc 1 (min m n) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    have h2 : ∀ k ∈ Finset.filter (fun k => ¬ k ≤ min m n) (Icc 1 (m + n)),
        cEntry m k * cEntry n k = 0 := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk
      unfold cEntry
      by_cases h : k ≤ m
      · have : ¬ k ≤ n := by omega
        simp [this]
      · simp [h]
    rw [h1, Finset.sum_eq_zero h2, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_Icc] at hk
    unfold cEntry
    rw [if_pos (by omega), if_pos (by omega)]
    field_simp
  rw [hsum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  rcases le_total m n with h | h
  · rw [min_eq_left h, max_eq_right h]
    push_cast
    field_simp
  · rw [min_eq_right h, max_eq_left h]
    push_cast
    field_simp

/-- Cesàro mean `(Cx)_n = (1/n) Σ_{k=1}^{n} x_k`. -/
noncomputable def cesaro (x : ℕ → ℝ) (n : ℕ) : ℝ := (∑ k ∈ Icc 1 n, x k) / n

/-- `(Dh)_n = n h_n − (n − 1) h_{n−1}`. -/
def Dop (h : ℕ → ℝ) (n : ℕ) : ℝ := n * h n - ((n : ℝ) - 1) * h (n - 1)

/-- `D C = I`. -/
theorem D_cesaro (x : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) : Dop (cesaro x) n = x n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold Dop cesaro
  have h1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h2 : (m : ℝ) ≠ 0 := by positivity
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

/-- Telescoping form of `‖Dh‖² = ⟨h, L h⟩`: with `L = DᵀD`,
`Σ_{n=1}^{N+1} (Dh)_n² = Σ_{n=1}^{N} n(n+1)(h_n − h_{n+1})² + (N+1) h_{N+1}²`. -/
theorem sum_D_sq (h : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ range (N + 1), (Dop h (i + 1)) ^ 2 =
      ∑ i ∈ range N, ((i : ℝ) + 1) * ((i : ℝ) + 2) * (h (i + 1) - h (i + 2)) ^ 2 +
        ((N : ℝ) + 1) * h (N + 1) ^ 2 := by
  induction N with
  | zero => simp [Dop]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (n := N)]
    simp only [Dop, Nat.add_sub_cancel]
    push_cast
    ring

/-- Key numerical lemma: with `a² = b² − 1`, `c² = b² + 1`, `b² ≥ 2`,
`b³ (2b − a − c) ≥ 1/4`. -/
theorem key_ineq (a b c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : 0 < b) (hb2 : 2 ≤ b ^ 2)
    (ha2 : a ^ 2 = b ^ 2 - 1) (hc2 : c ^ 2 = b ^ 2 + 1) :
    1 / 4 ≤ b ^ 3 * (2 * b - a - c) := by
  have hP0 : 0 ≤ a * c := mul_nonneg ha hc
  have hP2 : (a * c) ^ 2 = b ^ 4 - 1 := by
    have : (a * c) ^ 2 = a ^ 2 * c ^ 2 := by ring
    rw [this, ha2, hc2]; ring
  have hb4 : 4 ≤ b ^ 4 := by nlinarith
  -- (a c) b² ≤ b⁴ − 1/2
  have hP : (a * c) * b ^ 2 ≤ b ^ 4 - 1 / 2 := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 < b ^ 4 - 1 / 2 := by linarith
    have : (b ^ 4 - 1 / 2) ^ 2 < ((a * c) * b ^ 2) ^ 2 := by
      exact pow_lt_pow_left₀ hcon hpos.le (by norm_num)
    have e : ((a * c) * b ^ 2) ^ 2 = (b ^ 4 - 1) * b ^ 4 := by
      rw [mul_pow, hP2]; ring
    nlinarith
  -- (a + c)² ≤ 4b² − 1/b²
  have hsq : (a + c) ^ 2 * b ^ 2 ≤ 4 * b ^ 4 - 1 := by
    have : (a + c) ^ 2 = 2 * b ^ 2 + 2 * (a * c) := by
      nlinarith [ha2, hc2]
    rw [this]; nlinarith
  -- a + c ≤ 2b − 1/(4b³)
  have hb3 : 0 < b ^ 3 := by positivity
  have hT : b ^ 3 * (a + c) ≤ 2 * b ^ 4 - 1 / 4 := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 < 2 * b ^ 4 - 1 / 4 := by linarith
    have h1 : (2 * b ^ 4 - 1 / 4) ^ 2 < (b ^ 3 * (a + c)) ^ 2 :=
      pow_lt_pow_left₀ hcon hpos.le (by norm_num)
    have e : (b ^ 3 * (a + c)) ^ 2 = b ^ 4 * ((a + c) ^ 2 * b ^ 2) := by ring
    have hb4' : 0 < b ^ 4 := by positivity
    have : b ^ 4 * ((a + c) ^ 2 * b ^ 2) ≤ b ^ 4 * (4 * b ^ 4 - 1) :=
      mul_le_mul_of_nonneg_left hsq hb4'.le
    nlinarith [sq_nonneg (b ^ 4)]
  nlinarith

/-- `r k = √(k+1)`. -/
noncomputable def r (k : ℕ) : ℝ := Real.sqrt ((k : ℝ) + 1)

/-- Edge weight `n (n+1)` with `n = i + 1`. -/
def wt (i : ℕ) : ℝ := ((i : ℝ) + 1) * ((i : ℝ) + 2)

/-- Picone coefficients for the ground profile `n^{-1/2}`. -/
noncomputable def Aco (i : ℕ) : ℝ := wt i * (1 - r i / r (i + 1))
noncomputable def Bco (i : ℕ) : ℝ := wt i * (1 - r (i + 1) / r i)

lemma r_pos (k : ℕ) : 0 < r k := Real.sqrt_pos.mpr (by positivity)

lemma wt_nonneg (i : ℕ) : 0 ≤ wt i := by unfold wt; positivity

/-- Picone edge inequality: `w (a − b)² ≥ A a² + B b²`. -/
theorem edge_ineq (i : ℕ) (a b : ℝ) :
    Aco i * a ^ 2 + Bco i * b ^ 2 ≤ wt i * (a - b) ^ 2 := by
  have h0 := r_pos i
  have h1 := r_pos (i + 1)
  set ρ : ℝ := r i / r (i + 1) with hρ
  have hρpos : 0 < ρ := div_pos h0 h1
  have hinv : r (i + 1) / r i = 1 / ρ := by rw [hρ]; field_simp
  unfold Aco Bco
  rw [hinv]
  have key : (a - b) ^ 2 - ((1 - ρ) * a ^ 2 + (1 - 1 / ρ) * b ^ 2) = (ρ * a - b) ^ 2 / ρ := by
    field_simp; ring
  have hnn : 0 ≤ (ρ * a - b) ^ 2 / ρ := by positivity
  have hw := wt_nonneg i
  nlinarith [mul_nonneg hw hnn]

/-- The `B` coefficient shifted by one (`0` at the left end). -/
noncomputable def Bp : ℕ → ℝ
  | 0 => 0
  | j + 1 => Bco j

/-- Re-summation of the edge terms. -/
theorem sum_AB (g : ℕ → ℝ) (M : ℕ) :
    ∑ i ∈ range M, (Aco i * g i ^ 2 + Bco i * g (i + 1) ^ 2) =
      ∑ j ∈ range M, (Aco j + Bp j) * g j ^ 2 + Bp M * g M ^ 2 := by
  induction M with
  | zero => simp [Bp]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (n := M)]
    simp only [Bp]
    ring

/-- Every combined coefficient is at least `1/4`. -/
theorem coef_ge (j : ℕ) : 1 / 4 ≤ Aco j + Bp j := by
  rcases j with _ | m
  · -- j = 0: A₀ = 2 (1 − 1/√2)
    simp only [Aco, Bp, wt, r]
    norm_num
    have h2 : (8 : ℝ) / 7 ≤ Real.sqrt 2 := by
      apply Real.le_sqrt_of_sq_le; norm_num
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hinv : (Real.sqrt 2)⁻¹ ≤ 7 / 8 := by
      rw [inv_le_comm₀ hs (by norm_num)]; norm_num; linarith
    linarith
  · simp only [Aco, Bp, Bco, wt, r]
    push_cast
    set a : ℝ := Real.sqrt ((m : ℝ) + 1) with ha
    set b : ℝ := Real.sqrt ((m : ℝ) + 1 + 1) with hb
    set c : ℝ := Real.sqrt ((m : ℝ) + 1 + 1 + 1) with hc
    have ha0 : 0 < a := Real.sqrt_pos.mpr (by positivity)
    have hb0 : 0 < b := Real.sqrt_pos.mpr (by positivity)
    have hc0 : 0 < c := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hb2 : b ^ 2 = (m : ℝ) + 1 + 1 := Real.sq_sqrt (by positivity)
    have hc2 : c ^ 2 = (m : ℝ) + 1 + 1 + 1 := Real.sq_sqrt (by positivity)
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have key := key_ineq a b c ha0.le hc0.le hb0 (by nlinarith) (by nlinarith) (by nlinarith)
    have e1 : ((m : ℝ) + 1 + 1) * ((m : ℝ) + 1 + 2) * (1 - b / c) = b ^ 2 * c ^ 2 - b ^ 3 * c := by
      have : ((m : ℝ) + 1 + 1) * ((m : ℝ) + 1 + 2) = b ^ 2 * c ^ 2 := by rw [hb2, hc2]; ring
      rw [this]; field_simp
    have e2 : ((m : ℝ) + 1) * ((m : ℝ) + 2) * (1 - b / a) = a ^ 2 * b ^ 2 - a * b ^ 3 := by
      have : ((m : ℝ) + 1) * ((m : ℝ) + 2) = a ^ 2 * b ^ 2 := by rw [ha2, hb2]; ring
      rw [this]; field_simp
    rw [e1, e2]
    nlinarith [key, ha2, hb2, hc2]

/-- **The sharp-floor direction `L ≥ ¼ I`** (Hardy): for a sequence `g` with `g M = 0`,
`(1/4) Σ_{i<M} g_i² ≤ Σ_{i<M} (i+1)(i+2)(g_i − g_{i+1})²`. With `g_i = h_{i+1}` this reads
`(1/4) Σ_{n=1}^{M} h_n² ≤ Σ_{n=1}^{M} n(n+1)(h_n − h_{n+1})² = ⟨h, L h⟩`. -/
theorem hardy_floor (g : ℕ → ℝ) (M : ℕ) (hg : g M = 0) :
    (1 / 4) * ∑ i ∈ range M, g i ^ 2 ≤
      ∑ i ∈ range M, ((i : ℝ) + 1) * ((i : ℝ) + 2) * (g i - g (i + 1)) ^ 2 := by
  have h1 : (1 / 4) * ∑ i ∈ range M, g i ^ 2 ≤
      ∑ j ∈ range M, (Aco j + Bp j) * g j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ =>
      by nlinarith [coef_ge j, sq_nonneg (g j)])
  have h2 : ∑ j ∈ range M, (Aco j + Bp j) * g j ^ 2 =
      ∑ i ∈ range M, (Aco i * g i ^ 2 + Bco i * g (i + 1) ^ 2) := by
    rw [sum_AB, hg]; simp
  have h3 : ∑ i ∈ range M, (Aco i * g i ^ 2 + Bco i * g (i + 1) ^ 2) ≤
      ∑ i ∈ range M, wt i * (g i - g (i + 1)) ^ 2 :=
    Finset.sum_le_sum (fun i _ => edge_ineq i (g i) (g (i + 1)))
  calc (1 / 4) * ∑ i ∈ range M, g i ^ 2 ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := h3

end GppCesaroCasimir
