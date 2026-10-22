import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The one-prime GCD Gram: orthonormal basis, Parseval, and exact coefficient dual norms

Source: Codex, `work/codex/2026-10-21_gcd_coefficient_recovery_closability_zeta_threshold.md` §B
(GPP-bridge; the one-prime case of the `ε > 1/2` side, checked there with Wolfram for degrees
1–7). Daniel Toupin / Golden Physics Project, with AI assistance from Codex (statement) and Claude
Code (formalization).

At one prime the monomials `u_k = χ_p^k` have Gram `⟨u_i, u_j⟩ = r^{|i−j|}`, `r = p^{−ε}`; here `r`
is any real with `r² < 1`, and vectors are coefficient sequences on `range M` (`gram`).

* `gram_phi`: `φ₀ = u₀`, `φ_{k+1} = (u_{k+1} − r u_k)/√(1 − r²)` is orthonormal.
* `expand`: every coefficient vector is `∑_k coord_k φ_k`, with
  `coord₀ = ∑ a_i r^i` and `coord_{k+1} = √(1−r²) ∑_{i ≥ k+1} a_i r^{i−k−1}`.
* `gram_self_eq` (Parseval): `‖a‖² = ∑_k coord_k²`; in particular the Gram is positive
  semidefinite (`gram_self_nonneg`).
* `dual_norm_zero`: `|a₀|² ≤ ‖a‖²/(1 − r²)`, with equality at `φ₀ − (r/√(1−r²)) φ₁`.
* `dual_norm_succ`: for an interior index `1 ≤ j < M − 1`, `|a_j|² ≤ (1 + r²)/(1 − r²) · ‖a‖²`,
  with equality at `φ_j − r φ_{j+1}`.

These are Codex's one-prime dual norms `1/(1 − r²)` and `(1 + r²)/(1 − r²)`, now exact for every
finite truncation, nonterminal index and every `r` with `r² < 1`.

**Scope.** The tensor product over all primes, which gives
`‖coeff_n‖² = ζ(2ε) ∏_{p|n}(1 + p^{−2ε})` on the analytic Hardy subspace, and the operator-norm
statements of §B and §F are not formalized. The `ε ≤ 1/2` side is `GppGcdPacketClosability`.
No RH content.
-/

open Finset

namespace GppOnePrimeToeplitz

variable (r : ℝ)

/-- The one-prime Poisson/Haar Gram `⟨u_i, u_j⟩ = r^{|i−j|}`, on coefficient vectors over
`range M`. -/
noncomputable def gram (M : ℕ) (a b : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range M, ∑ j ∈ range M, a i * b j * r ^ (i - j + (j - i))

/-- The unit vector `δ_i`. -/
def delta (i : ℕ) : ℕ → ℝ := fun k => if k = i then 1 else 0

lemma gram_delta {M i j : ℕ} (hi : i < M) (hj : j < M) :
    gram r M (delta i) (delta j) = r ^ (i - j + (j - i)) := by
  simp only [gram, delta, ite_mul, one_mul, zero_mul]
  rw [sum_eq_single i (fun k _ hk => by simp [hk]) (fun h => absurd (mem_range.mpr hi) h)]
  simp only [if_true]
  rw [sum_eq_single j (fun k _ hk => by simp [hk]) (fun h => absurd (mem_range.mpr hj) h)]
  simp

lemma gram_add_left (M : ℕ) (a a' b : ℕ → ℝ) :
    gram r M (a + a') b = gram r M a b + gram r M a' b := by
  simp only [gram, Pi.add_apply, add_mul, sum_add_distrib]

lemma gram_add_right (M : ℕ) (a b b' : ℕ → ℝ) :
    gram r M a (b + b') = gram r M a b + gram r M a b' := by
  simp only [gram, Pi.add_apply, mul_add, add_mul, sum_add_distrib]

lemma gram_smul_left (M : ℕ) (c : ℝ) (a b : ℕ → ℝ) :
    gram r M (c • a) b = c * gram r M a b := by
  simp only [gram, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

lemma gram_smul_right (M : ℕ) (c : ℝ) (a b : ℕ → ℝ) :
    gram r M a (c • b) = c * gram r M a b := by
  simp only [gram, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- Codex's orthonormal basis: `φ₀ = u₀`, `φ_{k+1} = (u_{k+1} − r u_k)/√(1 − r²)`. -/
noncomputable def phi : ℕ → ℕ → ℝ
  | 0 => delta 0
  | k + 1 => (Real.sqrt (1 - r ^ 2))⁻¹ • delta (k + 1) +
      (-r * (Real.sqrt (1 - r ^ 2))⁻¹) • delta k

lemma pow_dist_succ (m n : ℕ) :
    r ^ (m + 1 - (n + 1) + (n + 1 - (m + 1))) = r ^ (m - n + (n - m)) := by
  congr 1; omega

/-- **Orthonormality** of `φ` in the Toeplitz Gram `r^{|i−j|}`, for `|r| < 1`. -/
theorem gram_phi {M : ℕ} (hr : r ^ 2 < 1) {k l : ℕ} (hk : k < M) (hl : l < M) :
    gram r M (phi r k) (phi r l) = if k = l then 1 else 0 := by
  have hs : (Real.sqrt (1 - r ^ 2)) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by linarith)
  have hs0 : Real.sqrt (1 - r ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  rcases k with _ | m <;> rcases l with _ | n
  · simp [phi, gram_delta r hk hl]
  · rw [if_neg (show (0 : ℕ) ≠ n + 1 by omega)]
    simp only [phi, gram_add_right, gram_smul_right, gram_delta r hk hl,
      gram_delta r hk (by omega : n < M)]
    have e1 : 0 - (n + 1) + (n + 1 - 0) = n + 1 := by omega
    have e2 : 0 - n + (n - 0) = n := by omega
    rw [e1, e2, pow_succ]; ring
  · rw [if_neg (show m + 1 ≠ 0 by omega)]
    simp only [phi, gram_add_left, gram_smul_left, gram_delta r hk hl,
      gram_delta r (by omega : m < M) hl]
    have e1 : m + 1 - 0 + (0 - (m + 1)) = m + 1 := by omega
    have e2 : m - 0 + (0 - m) = m := by omega
    rw [e1, e2, pow_succ]; ring
  · simp only [phi, gram_add_left, gram_add_right, gram_smul_left, gram_smul_right,
      gram_delta r hk hl, gram_delta r hk (by omega : n < M),
      gram_delta r (by omega : m < M) hl, gram_delta r (by omega : m < M) (by omega : n < M),
      pow_dist_succ, Nat.add_right_cancel_iff]
    rcases lt_trichotomy m n with hmn | rfl | hmn
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmn
      rw [if_neg (by omega)]
      have e1 : m + 1 - (m + d + 1) + (m + d + 1 - (m + 1)) = d := by omega
      have e3 : m - (m + d + 1) + (m + d + 1 - m) = d + 1 := by omega
      have e4 : m - (m + d + 1 + 1) + (m + d + 1 + 1 - m) = d + 2 := by omega
      rw [e1, e3, e4]
      ring
    · rw [if_pos rfl]
      have e2 : m + 1 - m + (m - (m + 1)) = 1 := by omega
      have e3 : m - (m + 1) + (m + 1 - m) = 1 := by omega
      have e4 : m - m + (m - m) = 0 := by omega
      rw [e2, e3, e4]
      field_simp
      linarith [hs]
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmn
      rw [if_neg (by omega)]
      have e2 : n + d + 1 + 1 - n + (n - (n + d + 1 + 1)) = d + 2 := by omega
      have e3 : n + d + 1 - (n + 1) + (n + 1 - (n + d + 1)) = d := by omega
      have e4 : n + d + 1 - n + (n - (n + d + 1)) = d + 1 := by omega
      rw [e2, e3, e4]
      ring

/-- The `φ`-coordinates of a coefficient vector `a` on `range M`. -/
noncomputable def coord (M : ℕ) (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => ∑ i ∈ range M, a i * r ^ i
  | k + 1 => Real.sqrt (1 - r ^ 2) * ∑ i ∈ Ico (k + 1) M, a i * r ^ (i - (k + 1))

lemma phi_apply_zero (j : ℕ) : phi r 0 j = if j = 0 then 1 else 0 := by
  simp [phi, delta]

lemma phi_apply_succ (k j : ℕ) : phi r (k + 1) j =
    (Real.sqrt (1 - r ^ 2))⁻¹ * (if j = k + 1 then 1 else 0) +
      -r * (Real.sqrt (1 - r ^ 2))⁻¹ * (if j = k then 1 else 0) := by
  simp only [phi, delta, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

lemma Ico_peel (a : ℕ → ℝ) {c M : ℕ} (hc : c < M) :
    ∑ i ∈ Ico c M, a i * r ^ (i - c) = a c + r * ∑ i ∈ Ico (c + 1) M, a i * r ^ (i - (c + 1)) := by
  rw [sum_eq_sum_Ico_succ_bot hc, Nat.sub_self, pow_zero, mul_one, mul_sum]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have := (mem_Ico.mp hi).1
  rw [show i - c = (i - (c + 1)) + 1 by omega, pow_succ]; ring

/-- **Expansion in the orthonormal basis.** Every coefficient vector on `range M` is
`∑_k coord_k φ_k`. -/
theorem expand (hr : r ^ 2 < 1) (M : ℕ) (a : ℕ → ℝ) {j : ℕ} (hj : j < M) :
    ∑ k ∈ range M, coord r M a k * phi r k j = a j := by
  have hs0 : Real.sqrt (1 - r ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [sum_range_succ']
  simp only [phi_apply_succ, phi_apply_zero, mul_add, sum_add_distrib]
  rcases j with _ | j
  · simp only [if_true, mul_one, show ∀ k : ℕ, (0 = k + 1) = False from
      fun k => by simp, if_false, mul_zero, sum_const_zero, zero_add]
    have h0 : coord r (M' + 1) a 0 = a 0 + r * ∑ i ∈ Ico 1 (M' + 1), a i * r ^ (i - 1) := by
      simp only [coord]
      rw [range_eq_Ico, ← Ico_peel r a (by omega : 0 < M' + 1)]
      simp
    rcases M' with _ | M''
    · simp [coord]
    · rw [sum_range_succ']
      simp only [show ∀ k : ℕ, (0 = k + 1) = False from fun k => by simp, if_false, mul_zero,
        sum_const_zero, zero_add, if_true, mul_one]
      rw [h0]
      simp only [coord, zero_add]
      field_simp
      ring
  · simp only [Nat.add_right_cancel_iff, show (j + 1 = 0) = False from by simp, if_false,
      mul_zero, add_zero]
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_range]
    rw [if_pos (by omega : j < M')]
    have hpeel := Ico_peel r a (by omega : j + 1 < M' + 1)
    simp only [coord]
    split_ifs with h
    · rw [hpeel]; field_simp; ring
    · have hj' : j + 1 = M' := by omega
      rw [hpeel, show Ico (j + 1 + 1) (M' + 1) = ∅ by
        rw [Finset.Ico_eq_empty_iff]; omega]
      field_simp; simp

lemma gram_congr {M : ℕ} {a a' b b' : ℕ → ℝ} (ha : ∀ i < M, a i = a' i)
    (hb : ∀ j < M, b j = b' j) : gram r M a b = gram r M a' b' := by
  unfold gram
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  rw [ha i (mem_range.mp hi), hb j (mem_range.mp hj)]

lemma gram_sum (M : ℕ) (c d : ℕ → ℝ) (f g : ℕ → ℕ → ℝ) :
    gram r M (fun i => ∑ k ∈ range M, c k * f k i) (fun j => ∑ l ∈ range M, d l * g l j) =
      ∑ k ∈ range M, ∑ l ∈ range M, c k * d l * gram r M (f k) (g l) := by
  unfold gram
  have step : ∀ i j : ℕ, (∑ k ∈ range M, c k * f k i) * (∑ l ∈ range M, d l * g l j) *
      r ^ (i - j + (j - i)) = ∑ k ∈ range M, ∑ l ∈ range M,
        c k * d l * (f k i * g l j * r ^ (i - j + (j - i))) := by
    intro i j
    rw [sum_mul_sum, sum_mul]
    exact sum_congr rfl fun k _ => by rw [sum_mul]; exact sum_congr rfl fun l _ => by ring
  simp_rw [step, mul_sum]
  -- reorder Σ_k Σ_l Σ_i Σ_j into Σ_i Σ_j Σ_k Σ_l
  symm
  calc ∑ k ∈ range M, ∑ l ∈ range M, ∑ i ∈ range M, ∑ j ∈ range M,
        c k * d l * (f k i * g l j * r ^ (i - j + (j - i)))
      = ∑ k ∈ range M, ∑ i ∈ range M, ∑ l ∈ range M, ∑ j ∈ range M,
        c k * d l * (f k i * g l j * r ^ (i - j + (j - i))) := sum_congr rfl fun _ _ => sum_comm
    _ = ∑ k ∈ range M, ∑ i ∈ range M, ∑ j ∈ range M, ∑ l ∈ range M,
        c k * d l * (f k i * g l j * r ^ (i - j + (j - i))) :=
          sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
    _ = ∑ i ∈ range M, ∑ k ∈ range M, ∑ j ∈ range M, ∑ l ∈ range M,
        c k * d l * (f k i * g l j * r ^ (i - j + (j - i))) := sum_comm
    _ = ∑ i ∈ range M, ∑ j ∈ range M, ∑ k ∈ range M, ∑ l ∈ range M,
        c k * d l * (f k i * g l j * r ^ (i - j + (j - i))) := sum_congr rfl fun _ _ => sum_comm

/-- **Parseval.** `‖a‖²_{gram} = ∑_k coord_k²`. In particular the Toeplitz Gram is positive. -/
theorem gram_self_eq (hr : r ^ 2 < 1) (M : ℕ) (a : ℕ → ℝ) :
    gram r M a a = ∑ k ∈ range M, coord r M a k ^ 2 := by
  have hx : ∀ i < M, a i = ∑ k ∈ range M, coord r M a k * phi r k i := fun i hi =>
    (expand r hr M a hi).symm
  rw [gram_congr r hx hx, gram_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [sum_eq_single k]
  · rw [gram_phi r hr (mem_range.mp hk) (mem_range.mp hk), if_pos rfl]; ring
  · intro l hl hlk
    rw [gram_phi r hr (mem_range.mp hk) (mem_range.mp hl), if_neg (Ne.symm hlk), mul_zero]
  · intro h; exact absurd hk h

lemma gram_self_nonneg (hr : r ^ 2 < 1) (M : ℕ) (a : ℕ → ℝ) : 0 ≤ gram r M a a := by
  rw [gram_self_eq r hr]; exact sum_nonneg fun _ _ => sq_nonneg _

/-- The coefficient of `u_j` (`1 ≤ j`, `j + 1 < M`) in `φ`-coordinates. -/
lemma coeff_succ_eq (hr : r ^ 2 < 1) {M : ℕ} (a : ℕ → ℝ) {j : ℕ} (hj : j + 1 + 1 < M) :
    a (j + 1) = (coord r M a (j + 1) - r * coord r M a (j + 1 + 1)) /
      Real.sqrt (1 - r ^ 2) := by
  have hs0 : Real.sqrt (1 - r ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  simp only [coord]
  rw [Ico_peel r a (by omega : j + 1 < M)]
  field_simp
  ring

/-- The coefficient of `u_0` in `φ`-coordinates (`1 < M`). -/
lemma coeff_zero_eq (hr : r ^ 2 < 1) {M : ℕ} (a : ℕ → ℝ) (hM : 1 < M) :
    a 0 = coord r M a 0 - r / Real.sqrt (1 - r ^ 2) * coord r M a 1 := by
  have hs0 : Real.sqrt (1 - r ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  simp only [coord]
  rw [range_eq_Ico, show (fun i => a i * r ^ i) = (fun i => a i * r ^ (i - 0)) by simp,
    Ico_peel r a (by omega : 0 < M)]
  field_simp
  simp

/-- **Dual norm of an interior coefficient.** For `1 ≤ j` and `j + 1 < M`,
`|a_j|² ≤ (1 + r²)/(1 − r²) · ‖a‖²`, with equality at `a = φ_j − r φ_{j+1}`. -/
theorem dual_norm_succ (hr : r ^ 2 < 1) {M j : ℕ} (hj : j + 1 + 1 < M) :
    (∀ a : ℕ → ℝ, a (j + 1) ^ 2 ≤ (1 + r ^ 2) / (1 - r ^ 2) * gram r M a a) ∧
      (phi r (j + 1) - r • phi r (j + 1 + 1)) (j + 1) ^ 2 = (1 + r ^ 2) / (1 - r ^ 2) *
        gram r M (phi r (j + 1) - r • phi r (j + 1 + 1))
          (phi r (j + 1) - r • phi r (j + 1 + 1)) := by
  have h1r : 0 < 1 - r ^ 2 := by linarith
  have hs : (Real.sqrt (1 - r ^ 2)) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt h1r.le
  have hs0 : Real.sqrt (1 - r ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h1r).ne'
  constructor
  · intro a
    set c := coord r M a
    have hsum : c (j + 1) ^ 2 + c (j + 1 + 1) ^ 2 ≤ gram r M a a := by
      rw [gram_self_eq r hr]
      have h2 : ({j + 1, j + 1 + 1} : Finset ℕ) ⊆ range M := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx; rw [mem_range]; omega
      calc c (j + 1) ^ 2 + c (j + 1 + 1) ^ 2 = ∑ k ∈ {j + 1, j + 1 + 1}, c k ^ 2 := by
            rw [sum_pair (by omega)]
        _ ≤ ∑ k ∈ range M, c k ^ 2 := sum_le_sum_of_subset_of_nonneg h2
            fun _ _ _ => sq_nonneg _
    rw [coeff_succ_eq r hr a hj, div_pow, hs]
    have hcs : (c (j + 1) - r * c (j + 1 + 1)) ^ 2 ≤
        (1 + r ^ 2) * (c (j + 1) ^ 2 + c (j + 1 + 1) ^ 2) := by
      nlinarith [sq_nonneg (r * c (j + 1) + c (j + 1 + 1))]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right h1r]
    calc (c (j + 1) - r * c (j + 1 + 1)) ^ 2
        ≤ (1 + r ^ 2) * (c (j + 1) ^ 2 + c (j + 1 + 1) ^ 2) := hcs
      _ ≤ (1 + r ^ 2) * gram r M a a := mul_le_mul_of_nonneg_left hsum (by positivity)
  · have hk1 : j + 1 < M := by omega
    rw [sub_eq_add_neg, ← neg_smul, gram_add_left, gram_add_right, gram_add_right,
      gram_smul_left, gram_smul_right, gram_smul_left, gram_smul_right,
      gram_phi r hr hk1 hk1, gram_phi r hr hk1 hj, gram_phi r hr hj hk1, gram_phi r hr hj hj]
    simp only [if_true, show j + 1 ≠ j + 1 + 1 by omega, show j + 1 + 1 ≠ j + 1 by omega,
      if_false, Pi.add_apply, Pi.smul_apply, smul_eq_mul, phi_apply_succ]
    simp only [show j + 1 ≠ j by omega, if_false, mul_one, mul_zero, add_zero]
    field_simp
    rw [hs]
    ring

/-- **Dual norm of the constant coefficient.** For `1 < M`, `|a_0|² ≤ 1/(1 − r²) · ‖a‖²`, with
equality at `a = φ₀ − (r/√(1−r²)) φ₁`. -/
theorem dual_norm_zero (hr : r ^ 2 < 1) {M : ℕ} (hM : 1 < M) :
    (∀ a : ℕ → ℝ, a 0 ^ 2 ≤ 1 / (1 - r ^ 2) * gram r M a a) ∧
      (phi r 0 - (r / Real.sqrt (1 - r ^ 2)) • phi r 1) 0 ^ 2 = 1 / (1 - r ^ 2) *
        gram r M (phi r 0 - (r / Real.sqrt (1 - r ^ 2)) • phi r 1)
          (phi r 0 - (r / Real.sqrt (1 - r ^ 2)) • phi r 1) := by
  have h1r : 0 < 1 - r ^ 2 := by linarith
  have hs : (Real.sqrt (1 - r ^ 2)) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt h1r.le
  have hs0 : Real.sqrt (1 - r ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h1r).ne'
  constructor
  · intro a
    set c := coord r M a
    have hsum : c 0 ^ 2 + c 1 ^ 2 ≤ gram r M a a := by
      rw [gram_self_eq r hr]
      have h2 : ({0, 1} : Finset ℕ) ⊆ range M := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx; rw [mem_range]; omega
      calc c 0 ^ 2 + c 1 ^ 2 = ∑ k ∈ {0, 1}, c k ^ 2 := by rw [sum_pair (by omega)]
        _ ≤ ∑ k ∈ range M, c k ^ 2 := sum_le_sum_of_subset_of_nonneg h2
            fun _ _ _ => sq_nonneg _
    rw [coeff_zero_eq r hr a hM]
    set t := r / Real.sqrt (1 - r ^ 2)
    have ht : 1 + t ^ 2 = 1 / (1 - r ^ 2) := by
      rw [div_pow, hs]; field_simp; ring
    have hcs : (c 0 - t * c 1) ^ 2 ≤ (1 + t ^ 2) * (c 0 ^ 2 + c 1 ^ 2) := by
      nlinarith [sq_nonneg (t * c 0 + c 1)]
    rw [← ht]
    calc (c 0 - t * c 1) ^ 2 ≤ (1 + t ^ 2) * (c 0 ^ 2 + c 1 ^ 2) := hcs
      _ ≤ (1 + t ^ 2) * gram r M a a := mul_le_mul_of_nonneg_left hsum (by positivity)
  · have h0 : 0 < M := by omega
    rw [sub_eq_add_neg, ← neg_smul, gram_add_left, gram_add_right, gram_add_right,
      gram_smul_left, gram_smul_right, gram_smul_left, gram_smul_right,
      gram_phi r hr h0 h0, gram_phi r hr h0 hM, gram_phi r hr hM h0, gram_phi r hr hM hM]
    simp only [if_true, show (0 : ℕ) ≠ 1 by omega, show (1 : ℕ) ≠ 0 by omega, if_false,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, phi_apply_zero]
    rw [show phi r 1 0 = _ from phi_apply_succ r 0 0]
    simp only [if_true, show (0 : ℕ) ≠ 0 + 1 by omega, if_false, mul_one, mul_zero, add_zero]
    field_simp
    rw [hs]
    ring

end GppOnePrimeToeplitz
