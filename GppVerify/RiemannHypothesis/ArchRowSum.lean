import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Dist

/-!
# Uniform-in-`K` norm bounds for geometrically decaying Toeplitz and folded Hankel blocks

Source: Codex, GPP-bridge PR #11 comment 6381970052 (Discovery2 #17/#18). Daniel Toupin /
Golden Physics Project, with AI assistance from Codex (statement) and Claude Code (formalization).

* `schur_test`: if every row and column of `|K|` sums to at most `R`, then
  `|vᵀ K v| ≤ R ‖v‖²`.
* `toeplitz_row_sum`: for a Toeplitz kernel `A(|i − j|)` on `{0, …, n−1}`, every row of `|A|`
  sums to at most `|A₀| + 2 ∑_{1 ≤ d < n} |A_d|`.
* `toeplitz_form_le`: hence `|vᵀ T v| ≤ (|A₀| + 2 ∑_{1 ≤ d < n} |A_d|) ‖v‖²`.
* `toeplitz_form_le_geom`: if `|A_d| ≤ |A₂| q^{d−2}` for `d ≥ 2` with `0 ≤ q < 1`, then
  `|vᵀ T v| ≤ (|A₀| + 2|A₁| + 2|A₂|/(1 − q)) ‖v‖²` for **every** `n`.
* `gram_form_le_trace`: for a finite family of vectors `h_λ` and `C = −∑_λ h_λ h_λᵀ`,
  `0 ≤ −vᵀ C v ≤ (∑_λ ‖h_λ‖²) ‖v‖²`. With `h_λ(j) = e^{−λ(a₀ + δj)} S(−λ)`,
  `‖h_λ‖² ≤ e^{−2λa₀} S(−λ)²/(1 − e^{−2λδ})` (`geom_partial_le`), uniformly in `K`.

**Scope.** Elementary bounds on the stated kernels. The identification of these kernels with
Discovery2's gamma Toeplitz entries `A_d` and Hankel vectors `h_λ` (the digamma reduction,
audited numerically in PR #11 6380867161) is not formalized, nor are the Arb enclosures of
`A₀, A₁`. As Codex notes, this bounds the *pure gamma Arch* blocks only; it does not rule out
compensation from the SQ, prime or pole parts. No claim about RH.
-/

open Finset

namespace GppArchRowSum

/-- **Schur test.** Row and column sums of `|K|` at most `R` give `|vᵀ K v| ≤ R ‖v‖²`. -/
theorem schur_test (s : Finset ℕ) (K : ℕ → ℕ → ℝ) (v : ℕ → ℝ) {R : ℝ}
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |K i j| ≤ R) (hcol : ∀ j ∈ s, ∑ i ∈ s, |K i j| ≤ R) :
    |∑ i ∈ s, ∑ j ∈ s, v i * v j * K i j| ≤ R * ∑ i ∈ s, v i ^ 2 := by
  have hpt : ∀ i j, 2 * |v i * v j * K i j| ≤ v i ^ 2 * |K i j| + v j ^ 2 * |K i j| := by
    intro i j
    rw [abs_mul, abs_mul]
    have h := two_mul_le_add_sq |v i| |v j|
    rw [sq_abs, sq_abs] at h
    nlinarith [abs_nonneg (K i j)]
  have h1 : ∑ i ∈ s, ∑ j ∈ s, v i ^ 2 * |K i j| ≤ R * ∑ i ∈ s, v i ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    rw [← mul_sum, mul_comm]
    exact mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg _)
  have h2 : ∑ i ∈ s, ∑ j ∈ s, v j ^ 2 * |K i j| ≤ R * ∑ i ∈ s, v i ^ 2 := by
    rw [sum_comm, mul_sum]
    refine sum_le_sum fun j hj => ?_
    rw [← mul_sum, mul_comm]
    exact mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg _)
  have h3 : 2 * ∑ i ∈ s, ∑ j ∈ s, |v i * v j * K i j| ≤
      ∑ i ∈ s, ∑ j ∈ s, v i ^ 2 * |K i j| + ∑ i ∈ s, ∑ j ∈ s, v j ^ 2 * |K i j| := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun i _ => ?_
    rw [mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun j _ => hpt i j
  have h4 : |∑ i ∈ s, ∑ j ∈ s, v i * v j * K i j| ≤ ∑ i ∈ s, ∑ j ∈ s, |v i * v j * K i j| :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
  linarith

/-- Indices below `i`, read as distances, land injectively in `[1, n)`. -/
lemma sum_below_le {n i : ℕ} (hi : i < n) (f : ℕ → ℝ) (hf : ∀ d, 0 ≤ f d) :
    ∑ j ∈ (range n).filter (· < i), f (i - j) ≤ ∑ d ∈ Ico 1 n, f d := by
  rw [← sum_image (g := fun j => i - j) (fun a ha b hb hab => by
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at ha hb
    simp only at hab
    omega)]
  refine sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) fun d _ _ => hf d
  simp only [mem_image, mem_filter, mem_range] at hd
  obtain ⟨j, ⟨_, hj⟩, rfl⟩ := hd
  simp only [mem_Ico]; omega

/-- Indices above `i`, read as distances, land injectively in `[1, n)`. -/
lemma sum_above_le {n i : ℕ} (f : ℕ → ℝ) (hf : ∀ d, 0 ≤ f d) :
    ∑ j ∈ (range n).filter (i < ·), f (j - i) ≤ ∑ d ∈ Ico 1 n, f d := by
  rw [← sum_image (g := fun j => j - i) (fun a ha b hb hab => by
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at ha hb
    simp only at hab
    omega)]
  refine sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) fun d _ _ => hf d
  simp only [mem_image, mem_filter, mem_range] at hd
  obtain ⟨j, ⟨hjn, hj⟩, rfl⟩ := hd
  simp only [mem_Ico]; omega

/-- **Toeplitz row sum.** `∑_{j<n} f(|i − j|) ≤ f 0 + 2 ∑_{1 ≤ d < n} f d` for `f ≥ 0`. -/
theorem toeplitz_row_sum {n i : ℕ} (hi : i < n) (f : ℕ → ℝ) (hf : ∀ d, 0 ≤ f d) :
    ∑ j ∈ range n, f (Nat.dist i j) ≤ f 0 + 2 * ∑ d ∈ Ico 1 n, f d := by
  rw [← sum_filter_add_sum_filter_not (range n) (· < i),
    ← sum_filter_add_sum_filter_not ((range n).filter fun j => ¬ j < i) (i < ·)]
  have hlow : ∑ j ∈ (range n).filter (· < i), f (Nat.dist i j) =
      ∑ j ∈ (range n).filter (· < i), f (i - j) :=
    sum_congr rfl fun j hj => by
      rw [mem_filter] at hj; rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hj.2.le]
  have hhigh : ∑ j ∈ ((range n).filter fun j => ¬ j < i).filter (i < ·), f (Nat.dist i j) =
      ∑ j ∈ (range n).filter (i < ·), f (j - i) := by
    rw [filter_filter]
    refine sum_congr (by ext j; simp only [mem_filter, mem_range]; omega) fun j hj => ?_
    rw [mem_filter] at hj; rw [Nat.dist_eq_sub_of_le hj.2.le]
  have hmid : ∑ j ∈ ((range n).filter fun j => ¬ j < i).filter (fun j => ¬ i < j),
      f (Nat.dist i j) = f 0 := by
    rw [filter_filter, show ((range n).filter fun j => ¬ j < i ∧ ¬ i < j) = {i} by
      ext j; simp only [mem_filter, mem_range, mem_singleton]; omega, sum_singleton,
      Nat.dist_self]
  rw [hlow, hhigh, hmid]
  linarith [sum_below_le hi f hf, sum_above_le (n := n) (i := i) f hf]

/-- **Toeplitz form bound.** `|vᵀ T v| ≤ (|A₀| + 2 ∑_{1 ≤ d < n} |A_d|) ‖v‖²`. -/
theorem toeplitz_form_le (n : ℕ) (A : ℕ → ℝ) (v : ℕ → ℝ) :
    |∑ i ∈ range n, ∑ j ∈ range n, v i * v j * A (Nat.dist i j)| ≤
      (|A 0| + 2 * ∑ d ∈ Ico 1 n, |A d|) * ∑ i ∈ range n, v i ^ 2 := by
  refine schur_test _ (fun i j => A (Nat.dist i j)) v (fun i hi => ?_) fun j hj => ?_
  · exact toeplitz_row_sum (mem_range.mp hi) (fun d => |A d|) fun d => abs_nonneg _
  · simp_rw [Nat.dist_comm _ j]
    exact toeplitz_row_sum (mem_range.mp hj) (fun d => |A d|) fun d => abs_nonneg _

/-- **Geometric partial sums.** `∑_{j<n} c r^j ≤ c/(1 − r)` for `c ≥ 0`, `0 ≤ r < 1`. -/
theorem geom_partial_le (n : ℕ) {c r : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ j ∈ range n, c * r ^ j ≤ c / (1 - r) := by
  rw [← mul_sum, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [← tsum_geometric_of_lt_one hr0 hr1]
  exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun j _ => pow_nonneg hr0 j)

/-- **All-`n` Toeplitz bound under geometric decay.** If `|A_d| ≤ |A₂| q^{d−2}` for `d ≥ 2`,
then `|vᵀ T v| ≤ (|A₀| + 2|A₁| + 2|A₂|/(1 − q)) ‖v‖²` for every `n`. -/
theorem toeplitz_form_le_geom (n : ℕ) (A : ℕ → ℝ) (v : ℕ → ℝ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hA : ∀ d, 2 ≤ d → |A d| ≤ |A 2| * q ^ (d - 2)) :
    |∑ i ∈ range n, ∑ j ∈ range n, v i * v j * A (Nat.dist i j)| ≤
      (|A 0| + 2 * |A 1| + 2 * (|A 2| / (1 - q))) * ∑ i ∈ range n, v i ^ 2 := by
  refine (toeplitz_form_le n A v).trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun i _ =>
    sq_nonneg _))
  have htail : ∑ d ∈ Ico 1 n, |A d| ≤ |A 1| + |A 2| / (1 - q) := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · calc ∑ d ∈ Ico 1 n, |A d| ≤ ∑ d ∈ Ico 1 2, |A d| :=
            sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right hn.le)
              fun d _ _ => abs_nonneg _
        _ = |A 1| := by simp
        _ ≤ |A 1| + |A 2| / (1 - q) := le_add_of_nonneg_right
            (div_nonneg (abs_nonneg _) (by linarith))
    · rw [← sum_Ico_consecutive _ (by norm_num : 1 ≤ 2) hn]
      simp only [Nat.Ico_succ_singleton, sum_singleton]
      have hT : ∑ d ∈ Ico 2 n, |A d| ≤ |A 2| / (1 - q) :=
        calc ∑ d ∈ Ico 2 n, |A d| ≤ ∑ d ∈ Ico 2 n, |A 2| * q ^ (d - 2) :=
              sum_le_sum fun d hd => hA d (mem_Ico.mp hd).1
          _ = ∑ j ∈ range (n - 2), |A 2| * q ^ j := by
              rw [sum_Ico_eq_sum_range]; exact sum_congr rfl fun j _ => by
                rw [show 2 + j - 2 = j by omega]
          _ ≤ |A 2| / (1 - q) := geom_partial_le _ (abs_nonneg _) hq0 hq1
      linarith
  linarith

/-- **Trace bound for a folded Gram block.** For `C = −∑_λ h_λ h_λᵀ`,
`0 ≤ −vᵀ C v ≤ (∑_λ ‖h_λ‖²) ‖v‖²`. -/
theorem gram_form_le_trace {ι : Type*} (L : Finset ι) (s : Finset ℕ) (h : ι → ℕ → ℝ)
    (v : ℕ → ℝ) :
    0 ≤ ∑ l ∈ L, (∑ i ∈ s, h l i * v i) ^ 2 ∧
      ∑ l ∈ L, (∑ i ∈ s, h l i * v i) ^ 2 ≤
        (∑ l ∈ L, ∑ i ∈ s, h l i ^ 2) * ∑ i ∈ s, v i ^ 2 := by
  refine ⟨sum_nonneg fun l _ => sq_nonneg _, ?_⟩
  rw [sum_mul]
  exact sum_le_sum fun l _ => sum_mul_sq_le_sq_mul_sq s (h l) v

end GppArchRowSum
