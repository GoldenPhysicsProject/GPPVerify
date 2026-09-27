import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Cutoff-independent Schur bound for half-density arithmetic synthesis

Source: Codex, GPPDiscovery2 `discovery/rh/RH_RIEMANN_SEED_SYNTHESIS_BOUND_2026-09-24.md`,
§§3–4 (formalized here 2026-09-27).

The note synthesizes `C e_n = n^{-1/2} T_{log n} φ` from the Archimedean Riemann seed `φ`, so the
Gram matrix is `G_{mn} = (mn)^{-1/2} K(log n - log m)` with `K(a) = ⟨φ, T_a φ⟩`. The seed has
`|K(a)| ≤ A_q e^{-q|a|}` for `0 < q < 5/2` (note §§2–3: Cauchy–Schwarz against the weighted
norms `N(±q)`, which are finite Gamma integrals). For `1/2 < q`, the note's Schur test then gives

  ‖C‖² ≤ A_q (2 + 1/(q - 1/2) + 1/(q + 1/2)),

independently of the finite arithmetic set `S`.

## Proved here

* `schurWeight_eq`: `(mn)^{-1/2} e^{-q|log n - log m|}` is the explicit weight
  `m^{q-1/2} n^{-(q+1/2)}` (for `m ≤ n`) and its mirror;
* `schurWeight_row_sum`: every row sum over any finite `S ⊆ {1, …, N}` is at most
  `R_q = 2 + 1/(q - 1/2) + 1/(q + 1/2)`, uniformly in `m`, `S` and `N`
  (sum–integral comparison on each side of the diagonal);
* `schur_quadratic`: the quadratic-form Schur test for a symmetric row-bounded weight;
* `synthesis_bound`: in any real inner-product space, if `⟪v m, v n⟫ = (mn)^{-1/2} K(log n - log m)`
  with `|K a| ≤ A e^{-q|a|}` and `q > 1/2`, then
  `‖Σ_{n ∈ S} c_n v_n‖² ≤ A · R_q · Σ_{n ∈ S} c_n²`.

## Taken as hypotheses

The decay `|K a| ≤ A e^{-q|a|}` of the seed autocorrelation (note §§2–3) and the identification
of the Gram entries with translates of the seed are hypotheses here, not derived from an `L²`
model of `φ`. The note's closed form for `N(q)²` is not formalized. Nothing here identifies the
Weil quadratic form with a positive Schur complement, and it is not a step that proves RH.
-/

open Real Finset MeasureTheory

namespace GppSeedSynthesisBound

/-- The explicit Schur weight `m^{q-1/2} n^{-(q+1/2)}` for `m ≤ n`, mirrored for `n < m`. -/
noncomputable def schurWeight (q : ℝ) (m n : ℕ) : ℝ :=
  if m ≤ n then (m : ℝ) ^ (q - 1 / 2) * (n : ℝ) ^ (-(q + 1 / 2))
  else (n : ℝ) ^ (q - 1 / 2) * (m : ℝ) ^ (-(q + 1 / 2))

/-- The uniform row-sum constant `R_q = 2 + 1/(q - 1/2) + 1/(q + 1/2)`. -/
noncomputable def rowConst (q : ℝ) : ℝ := 2 + 1 / (q - 1 / 2) + 1 / (q + 1 / 2)

lemma schurWeight_nonneg (q : ℝ) (m n : ℕ) : 0 ≤ schurWeight q m n := by
  unfold schurWeight
  split_ifs <;> positivity

lemma schurWeight_symm (q : ℝ) (m n : ℕ) : schurWeight q m n = schurWeight q n m := by
  unfold schurWeight
  rcases lt_trichotomy m n with h | rfl | h
  · rw [if_pos h.le, if_neg (not_le.mpr h)]
  · rfl
  · rw [if_neg (not_le.mpr h), if_pos h.le]

/-- The weight is the note's `(mn)^{-1/2} e^{-q |log n - log m|}`. -/
lemma schurWeight_eq (q : ℝ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    schurWeight q m n =
      ((m : ℝ) * n) ^ (-(1 / 2 : ℝ)) * Real.exp (-q * |Real.log n - Real.log m|) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.mul_rpow hm0.le hn0.le, Real.rpow_def_of_pos hm0, Real.rpow_def_of_pos hn0]
  unfold schurWeight
  split_ifs with h
  · have hlog : Real.log m ≤ Real.log n := Real.log_le_log hm0 (by exact_mod_cast h)
    rw [abs_of_nonneg (by linarith), Real.rpow_def_of_pos hm0, Real.rpow_def_of_pos hn0,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · have hlog : Real.log n ≤ Real.log m :=
      Real.log_le_log hn0 (by exact_mod_cast (not_le.mp h).le)
    rw [abs_of_nonpos (by linarith), Real.rpow_def_of_pos hm0, Real.rpow_def_of_pos hn0,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

/-- Tail sum: `Σ_{m ≤ n ≤ N} n^{-s} ≤ m^{-s} + m^{1-s}/(s-1)` for `s > 1`. -/
lemma tail_sum_le (s : ℝ) (hs : 1 < s) {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ∑ n ∈ Icc m N, (n : ℝ) ^ (-s) ≤ (m : ℝ) ^ (-s) + (m : ℝ) ^ (1 - s) / (s - 1) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos : 0 ≤ (m : ℝ) ^ (1 - s) / (s - 1) := div_nonneg (by positivity) (by linarith)
  rcases lt_or_ge N m with hN | hN
  · rw [Icc_eq_empty (by omega), sum_empty]
    positivity
  rw [← Ioc_insert_left hN, sum_insert left_notMem_Ioc, add_le_add_iff_left]
  have hIoc : ∑ n ∈ Ioc m N, (n : ℝ) ^ (-s) = ∑ i ∈ Ico m N, ((i + 1 : ℕ) : ℝ) ^ (-s) := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, ← sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ (-s)) m N 1]
  rw [hIoc]
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc (m : ℝ) N) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hm0.trans_le hx.1) hxy (by linarith)
  refine (hanti.sum_le_integral_Ico hN).trans ?_
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [Set.uIcc_of_le (by exact_mod_cast hN)]
    exact fun h => absurd h.1 (not_le.mpr hm0)⟩)]
  have h1 : (0 : ℝ) ≤ (N : ℝ) ^ (1 - s) := by positivity
  have e : ((N : ℝ) ^ (-s + 1) - (m : ℝ) ^ (-s + 1)) / (-s + 1) =
      ((m : ℝ) ^ (1 - s) - (N : ℝ) ^ (1 - s)) / (s - 1) := by
    rw [show -s + 1 = 1 - s by ring, div_eq_div_iff (by linarith) (by linarith)]
    ring
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- Head sum: `Σ_{1 ≤ n ≤ m} n^r ≤ m^r + m^{r+1}/(r+1)` for `r > 0`. -/
lemma head_sum_le (r : ℝ) (hr : 0 < r) (m : ℕ) :
    ∑ n ∈ Icc 1 m, (n : ℝ) ^ r ≤ (m : ℝ) ^ r + (m : ℝ) ^ (r + 1) / (r + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0), sum_empty, Nat.cast_zero]
    rw [Real.zero_rpow hr.ne', Real.zero_rpow (by linarith)]
    simp
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_succ_top (by omega), add_comm]
  gcongr
  have hmono : MonotoneOn (fun x : ℝ => x ^ r) (Set.Icc ((1 : ℕ) : ℝ) m) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow (by linarith [hx.1, show ((1 : ℕ) : ℝ) = 1 from Nat.cast_one]) hxy
      hr.le
  refine (hmono.sum_le_integral_Ico (by omega)).trans ?_
  rw [integral_rpow (Or.inl (by linarith))]
  push_cast
  rw [Real.one_rpow]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

lemma rpow_pair {m : ℕ} (hm : 1 ≤ m) (a b : ℝ) :
    (m : ℝ) ^ a * (m : ℝ) ^ b = (m : ℝ) ^ (a + b) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Real.rpow_add hm0]

/-- **Uniform row sums.** For `q > 1/2`, `m ≥ 1` and any `S ⊆ {1, …, N}`,
`Σ_{n ∈ S} W_q(m, n) ≤ 2 + 1/(q - 1/2) + 1/(q + 1/2)`. -/
theorem schurWeight_row_sum (q : ℝ) (hq : 1 / 2 < q) {m : ℕ} (hm : 1 ≤ m) (N : ℕ)
    (S : Finset ℕ) (hS : S ⊆ Icc 1 N) :
    ∑ n ∈ S, schurWeight q m n ≤ rowConst q := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hminv : (m : ℝ) ^ (-1 : ℝ) ≤ 1 := by
    rw [Real.rpow_neg_one]; exact inv_le_one_of_one_le₀ (by exact_mod_cast hm)
  refine (sum_le_sum_of_subset_of_nonneg hS
    (fun n _ _ => schurWeight_nonneg q m n)).trans ?_
  rw [← sum_filter_add_sum_filter_not (Icc 1 N) (fun n => m ≤ n)]
  -- upper side `n ≥ m`
  have hup : ∑ n ∈ (Icc 1 N).filter (fun n => m ≤ n), schurWeight q m n ≤
      1 + 1 / (q - 1 / 2) := by
    calc ∑ n ∈ (Icc 1 N).filter (fun n => m ≤ n), schurWeight q m n
        = ∑ n ∈ (Icc 1 N).filter (fun n => m ≤ n),
            (m : ℝ) ^ (q - 1 / 2) * (n : ℝ) ^ (-(q + 1 / 2)) := by
          refine sum_congr rfl (fun n hn => ?_)
          rw [schurWeight, if_pos (mem_filter.mp hn).2]
      _ ≤ ∑ n ∈ Icc m N, (m : ℝ) ^ (q - 1 / 2) * (n : ℝ) ^ (-(q + 1 / 2)) := by
          refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun _ _ _ => by positivity)
          obtain ⟨h1, h2⟩ := mem_filter.mp hn
          exact mem_Icc.mpr ⟨h2, (mem_Icc.mp h1).2⟩
      _ = (m : ℝ) ^ (q - 1 / 2) * ∑ n ∈ Icc m N, (n : ℝ) ^ (-(q + 1 / 2)) := by
          rw [mul_sum]
      _ ≤ (m : ℝ) ^ (q - 1 / 2) * ((m : ℝ) ^ (-(q + 1 / 2)) +
            (m : ℝ) ^ (1 - (q + 1 / 2)) / (q + 1 / 2 - 1)) := by
          gcongr
          exact tail_sum_le (q + 1 / 2) (by linarith) hm N
      _ = (m : ℝ) ^ (-1 : ℝ) + 1 / (q - 1 / 2) := by
          rw [mul_add, rpow_pair hm, mul_div_assoc', rpow_pair hm]
          rw [show q - 1 / 2 + -(q + 1 / 2) = (-1 : ℝ) by ring,
            show q - 1 / 2 + (1 - (q + 1 / 2)) = (0 : ℝ) by ring, Real.rpow_zero,
            show q + 1 / 2 - 1 = q - 1 / 2 by ring]
      _ ≤ 1 + 1 / (q - 1 / 2) := by linarith
  -- lower side `n < m`
  have hlo : ∑ n ∈ (Icc 1 N).filter (fun n => ¬ m ≤ n), schurWeight q m n ≤
      1 + 1 / (q + 1 / 2) := by
    calc ∑ n ∈ (Icc 1 N).filter (fun n => ¬ m ≤ n), schurWeight q m n
        = ∑ n ∈ (Icc 1 N).filter (fun n => ¬ m ≤ n),
            (n : ℝ) ^ (q - 1 / 2) * (m : ℝ) ^ (-(q + 1 / 2)) := by
          refine sum_congr rfl (fun n hn => ?_)
          rw [schurWeight, if_neg (mem_filter.mp hn).2]
      _ ≤ ∑ n ∈ Icc 1 m, (n : ℝ) ^ (q - 1 / 2) * (m : ℝ) ^ (-(q + 1 / 2)) := by
          refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun _ _ _ => by positivity)
          obtain ⟨h1, h2⟩ := mem_filter.mp hn
          exact mem_Icc.mpr ⟨(mem_Icc.mp h1).1, (not_le.mp h2).le⟩
      _ = (m : ℝ) ^ (-(q + 1 / 2)) * ∑ n ∈ Icc 1 m, (n : ℝ) ^ (q - 1 / 2) := by
          rw [mul_sum]; exact sum_congr rfl (fun _ _ => mul_comm _ _)
      _ ≤ (m : ℝ) ^ (-(q + 1 / 2)) * ((m : ℝ) ^ (q - 1 / 2) +
            (m : ℝ) ^ (q - 1 / 2 + 1) / (q - 1 / 2 + 1)) := by
          gcongr
          exact head_sum_le (q - 1 / 2) (by linarith) m
      _ = (m : ℝ) ^ (-1 : ℝ) + 1 / (q + 1 / 2) := by
          rw [mul_add, rpow_pair hm, mul_div_assoc', rpow_pair hm]
          rw [show -(q + 1 / 2) + (q - 1 / 2) = (-1 : ℝ) by ring,
            show -(q + 1 / 2) + (q - 1 / 2 + 1) = (0 : ℝ) by ring, Real.rpow_zero,
            show q - 1 / 2 + 1 = q + 1 / 2 by ring]
      _ ≤ 1 + 1 / (q + 1 / 2) := by linarith
  unfold rowConst
  linarith

/-- **Schur test (quadratic form).** If `|G m n| ≤ A · W m n` with `W` symmetric, nonnegative,
and every row sum of `W` over `S` at most `R`, then `Σ c_m c_n G_{mn} ≤ A R Σ c_m²`. -/
theorem schur_quadratic (S : Finset ℕ) (G W : ℕ → ℕ → ℝ) (A R : ℝ) (hA : 0 ≤ A)
    (hW0 : ∀ m n, 0 ≤ W m n) (hWs : ∀ m n, W m n = W n m)
    (hrow : ∀ m ∈ S, ∑ n ∈ S, W m n ≤ R) (hG : ∀ m ∈ S, ∀ n ∈ S, |G m n| ≤ A * W m n)
    (c : ℕ → ℝ) :
    ∑ m ∈ S, ∑ n ∈ S, c m * c n * G m n ≤ A * R * ∑ m ∈ S, c m ^ 2 := by
  have key : ∀ m ∈ S, ∀ n ∈ S, c m * c n * G m n ≤
      A * W m n * (c m ^ 2 / 2) + A * W n m * (c n ^ 2 / 2) := by
    intro m hm n hn
    rw [← hWs m n]
    have h1 : c m * c n * G m n ≤ |c m * c n| * |G m n| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 : |c m * c n| ≤ (c m ^ 2 + c n ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|c m| - |c n|), sq_abs (c m), sq_abs (c n)]
    have h3 := hG m hm n hn
    have hAW : 0 ≤ A * W m n := mul_nonneg hA (hW0 m n)
    calc c m * c n * G m n ≤ |c m * c n| * |G m n| := h1
      _ ≤ ((c m ^ 2 + c n ^ 2) / 2) * (A * W m n) :=
          mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  calc ∑ m ∈ S, ∑ n ∈ S, c m * c n * G m n
      ≤ ∑ m ∈ S, ∑ n ∈ S, (A * W m n * (c m ^ 2 / 2) + A * W n m * (c n ^ 2 / 2)) :=
        sum_le_sum (fun m hm => sum_le_sum (fun n hn => key m hm n hn))
    _ = ∑ m ∈ S, ∑ n ∈ S, A * W m n * (c m ^ 2 / 2) +
          ∑ m ∈ S, ∑ n ∈ S, A * W n m * (c n ^ 2 / 2) := by
        simp only [sum_add_distrib]
    _ = ∑ m ∈ S, (A * c m ^ 2) * ∑ n ∈ S, W m n := by
        rw [show ∑ m ∈ S, ∑ n ∈ S, A * W n m * (c n ^ 2 / 2) =
            ∑ m ∈ S, ∑ n ∈ S, A * W m n * (c m ^ 2 / 2) from sum_comm, ← sum_add_distrib]
        refine sum_congr rfl (fun m _ => ?_)
        rw [← sum_add_distrib, mul_sum]
        exact sum_congr rfl (fun n _ => by ring)
    _ ≤ ∑ m ∈ S, (A * c m ^ 2) * R :=
        sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left (hrow m hm) (by positivity))
    _ = A * R * ∑ m ∈ S, c m ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl (fun _ _ => by ring)

/-- **Cutoff-independent synthesis bound.** Let `v n` be vectors in a real inner-product space
whose Gram entries are half-density translates of a kernel with exponential decay:
`⟪v m, v n⟫ = (mn)^{-1/2} K(log n - log m)` and `|K a| ≤ A e^{-q|a|}` with `q > 1/2`.
Then for every finite `S` of positive integers,
`‖Σ_{n ∈ S} c_n v_n‖² ≤ A (2 + 1/(q - 1/2) + 1/(q + 1/2)) Σ_{n ∈ S} c_n²`. -/
theorem synthesis_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E) (K : ℝ → ℝ) (A q : ℝ) (hA : 0 ≤ A) (hq : 1 / 2 < q)
    (hgram : ∀ m n, 1 ≤ m → 1 ≤ n →
      inner ℝ (v m) (v n) = ((m : ℝ) * n) ^ (-(1 / 2 : ℝ)) * K (Real.log n - Real.log m))
    (hK : ∀ a, |K a| ≤ A * Real.exp (-q * |a|))
    (S : Finset ℕ) (hS0 : 0 ∉ S) (c : ℕ → ℝ) :
    ‖∑ n ∈ S, c n • v n‖ ^ 2 ≤ A * rowConst q * ∑ n ∈ S, c n ^ 2 := by
  have hpos : ∀ n ∈ S, 1 ≤ n := fun n hn =>
    Nat.one_le_iff_ne_zero.mpr (fun h => hS0 (h ▸ hn))
  set N := S.sup id
  have hSsub : S ⊆ Icc 1 N := fun n hn =>
    mem_Icc.mpr ⟨hpos n hn, le_sup (f := id) hn⟩
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right]
  calc _ = ∑ m ∈ S, ∑ n ∈ S, c m * c n * inner ℝ (v m) (v n) :=
        sum_congr rfl (fun m _ => sum_congr rfl (fun n _ => by ring))
    _ ≤ A * rowConst q * ∑ m ∈ S, c m ^ 2 := by
        refine schur_quadratic S (fun m n => inner ℝ (v m) (v n)) (schurWeight q) A
          (rowConst q) hA (schurWeight_nonneg q) (schurWeight_symm q)
          (fun m hm => schurWeight_row_sum q hq (hpos m hm) N S hSsub) ?_ c
        intro m hm n hn
        have hm1 := hpos m hm
        have hn1 := hpos n hn
        rw [hgram m n hm1 hn1, schurWeight_eq q hm1 hn1, abs_mul,
          abs_of_nonneg (by positivity)]
        calc ((m : ℝ) * n) ^ (-(1 / 2 : ℝ)) * |K (Real.log n - Real.log m)|
            ≤ ((m : ℝ) * n) ^ (-(1 / 2 : ℝ)) *
                (A * Real.exp (-q * |Real.log n - Real.log m|)) :=
              mul_le_mul_of_nonneg_left (hK _) (by positivity)
          _ = A * (((m : ℝ) * n) ^ (-(1 / 2 : ℝ)) *
                Real.exp (-q * |Real.log n - Real.log m|)) := by ring

end GppSeedSynthesisBound
