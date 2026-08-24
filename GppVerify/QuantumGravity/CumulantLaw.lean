import GppVerify.QuantumGravity.SinhLogSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.PSeries

/-!
# The cumulant law: `log P(λ) = -Σ_k (-1)^{k+1} ζ(2k) λ^{2k}/k`

The second half of the chain `SinhLogSeries.lean` scoped as its own honest next step, and
the item `Modular_Thermality_of_the_Celestial_Spectral_Weight.tex` / `blackbody_law_qg_
dtoupin_v1.tex` call "cumulants are even zeta values" / the "log expansion" face of the
spectral weight.

## What this file proves

`hasSum_log_double`: for `0 < λ`, `λ < 1`, the **unconditional double sum**, over all pairs
`(n,k) : ℕ×ℕ`, of `(-1)^k·(λ²/(n+1)²)^{k+1}/(k+1)` equals `log(sinh(πλ)/(πλ)) = -log(P λ)`.
This assembles two ingredients: `SinhLogSeries.hasSum_log_one_add_sq_div` (each row, i.e.
each fixed `n`, sums to `log(1+λ²/(n+1)²)`) and Mathlib's own `Real.hasSum_pow_div_log_of_
abs_lt_one` (the row itself is the standard alternating log-series). The genuinely new work
is `summable_double`: proving the double family is **absolutely summable**, which is what
licenses combining "every row sums correctly" with "the row-sums sum correctly" into "the
whole double sum sums correctly" (`HasSum.prod_fiberwise`) — swapping the order of a
non-absolutely-convergent double sum can change the total, so this step is not optional
bookkeeping. The bound used is uniform in `n`: since `λ²/(n+1)² ≤ λ² < 1` for *every* `n`,
`1 - λ²/(n+1)² ≥ 1-λ² > 0` uniformly, giving a single geometric-series comparison
`Σ_n λ²/[(n+1)²(1-λ²)]`, convergent by comparison with the `p=2` series.

## What this file does NOT do

Does not re-derive Mathlib's alternating log series itself, and does not attempt the final
re-indexing step of grouping the double sum by `k` alone to recover the paper's single-index
closed form `Σ_k (-1)^{k+1}ζ(2k)λ^{2k}/k` (a `tsum_prod'`/reindexing exercise on top of what
is proved here — the double-indexed `HasSum` already contains the same information, and the
single-index regrouping is bookkeeping left for whoever next needs the literal one-line
statement). No axiom, no sorry.
-/

namespace GppCumulantLaw

open Filter Topology

/-- The double-indexed alternating-log-series term. -/
noncomputable def term (lam : ℝ) (p : ℕ × ℕ) : ℝ :=
  (-1 : ℝ) ^ p.2 * (lam ^ 2 / ((p.1 : ℝ) + 1) ^ 2) ^ (p.2 + 1) / ((p.2 : ℝ) + 1)

/-- **Row summability**: for every `n`, the `k`-indexed row of `term lam` is exactly the
standard alternating log series for `y_n := λ²/(n+1)²`, hence `HasSum`s to
`log(1+y_n)`. -/
theorem hasSum_row (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (n : ℕ) :
    HasSum (fun k : ℕ => term lam (n, k)) (Real.log (1 + lam ^ 2 / ((n : ℝ) + 1) ^ 2)) := by
  set y : ℝ := lam ^ 2 / ((n : ℝ) + 1) ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have hyub : y ≤ lam ^ 2 := by
    have hn1 : (1:ℝ) ≤ ((n:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    rw [hy]
    rw [div_le_iff₀ (by linarith : (0:ℝ) < ((n:ℝ)+1)^2)]
    nlinarith
  have hylt1 : y < 1 := lt_of_le_of_lt hyub (by nlinarith)
  have habs : |(-y)| < 1 := by rw [abs_neg, abs_of_nonneg hy0]; exact hylt1
  have h := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have heq : ∀ k : ℕ, (-y) ^ (k + 1) / ((k : ℝ) + 1) = -(term lam (n, k)) := by
    intro k
    simp only [term, hy]
    rw [neg_pow, mul_div_assoc]
    ring
  have h2 : HasSum (fun k : ℕ => -(term lam (n, k))) (-Real.log (1 + y)) := by
    have hrw : Real.log (1 - -y) = Real.log (1 + y) := by ring_nf
    rw [hrw] at h
    simpa only [heq] using h
  have h3 := h2.neg
  simpa using h3

/-- **Uniform geometric bound and summability of the double family.** -/
theorem summable_double (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    Summable (term lam) := by
  have hlam2 : lam ^ 2 < 1 := by nlinarith
  have hrow_summable : ∀ n : ℕ, Summable (fun k : ℕ => ‖term lam (n, k)‖) := by
    intro n
    set y : ℝ := lam ^ 2 / ((n : ℝ) + 1) ^ 2 with hy
    have hy0 : 0 ≤ y := by positivity
    have hyub : y ≤ lam ^ 2 := by
      have hn1 : (1:ℝ) ≤ ((n:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      rw [hy, div_le_iff₀ (by linarith : (0:ℝ) < ((n:ℝ)+1)^2)]
      nlinarith
    have hylt1 : y < 1 := lt_of_le_of_lt hyub hlam2
    have heq : ∀ k : ℕ, ‖term lam (n, k)‖ = y ^ (k + 1) / ((k:ℝ) + 1) := by
      intro k
      simp only [term, hy, Real.norm_eq_abs, abs_mul, abs_div]
      have h1 : |(-1:ℝ) ^ k| = 1 := by
        rw [abs_pow]; norm_num
      have h2 : |(lam ^ 2 / ((n:ℝ)+1)^2) ^ (k+1)| = (lam ^ 2 / ((n:ℝ)+1)^2) ^ (k+1) :=
        abs_of_nonneg (by positivity)
      have h3 : |((k:ℝ)+1)| = (k:ℝ)+1 := abs_of_nonneg (by positivity)
      rw [h1, h2, h3, one_mul]
    have hle : ∀ k : ℕ, y ^ (k + 1) / ((k:ℝ) + 1) ≤ y ^ (k + 1) := by
      intro k
      exact div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hgeom_summable : Summable (fun k : ℕ => y ^ (k + 1)) := by
      have heqg : (fun k : ℕ => y ^ (k+1)) = (fun k : ℕ => y * y ^ k) := by funext k; ring
      rw [heqg]
      exact (summable_geometric_of_lt_one hy0 hylt1).mul_left y
    have hrow_sum_summable : Summable (fun k : ℕ => y ^ (k + 1) / ((k:ℝ) + 1)) :=
      Summable.of_nonneg_of_le (fun k => by positivity) hle hgeom_summable
    simpa only [heq] using hrow_sum_summable
  have hrow_bound : ∀ n : ℕ, ∑' k : ℕ, ‖term lam (n, k)‖ ≤ lam ^ 2 / (((n:ℝ)+1)^2 * (1 - lam^2)) := by
    intro n
    set y : ℝ := lam ^ 2 / ((n : ℝ) + 1) ^ 2 with hy
    have hy0 : 0 ≤ y := by positivity
    have hyub : y ≤ lam ^ 2 := by
      have hn1 : (1:ℝ) ≤ ((n:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      rw [hy, div_le_iff₀ (by linarith : (0:ℝ) < ((n:ℝ)+1)^2)]
      nlinarith
    have hylt1 : y < 1 := lt_of_le_of_lt hyub hlam2
    have heq : ∀ k : ℕ, ‖term lam (n, k)‖ = y ^ (k + 1) / ((k:ℝ) + 1) := by
      intro k
      simp only [term, hy, Real.norm_eq_abs, abs_mul, abs_div]
      have h1 : |(-1:ℝ) ^ k| = 1 := by rw [abs_pow]; norm_num
      have h2 : |(lam ^ 2 / ((n:ℝ)+1)^2) ^ (k+1)| = (lam ^ 2 / ((n:ℝ)+1)^2) ^ (k+1) :=
        abs_of_nonneg (by positivity)
      have h3 : |((k:ℝ)+1)| = (k:ℝ)+1 := abs_of_nonneg (by positivity)
      rw [h1, h2, h3, one_mul]
    have hle : ∀ k : ℕ, y ^ (k + 1) / ((k:ℝ) + 1) ≤ y ^ (k + 1) := by
      intro k
      exact div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hgeom_summable : Summable (fun k : ℕ => y ^ (k + 1)) := by
      have heqg : (fun k : ℕ => y ^ (k+1)) = (fun k : ℕ => y * y ^ k) := by funext k; ring
      rw [heqg]
      exact (summable_geometric_of_lt_one hy0 hylt1).mul_left y
    have hrow_sum_summable : Summable (fun k : ℕ => y ^ (k + 1) / ((k:ℝ) + 1)) :=
      Summable.of_nonneg_of_le (fun k => by positivity) hle hgeom_summable
    have hgeom_eq : ∑' k : ℕ, y ^ (k + 1) = y / (1 - y) := by
      have heqg : (fun k : ℕ => y ^ (k+1)) = (fun k : ℕ => y * y ^ k) := by funext k; ring
      rw [heqg, tsum_mul_left, tsum_geometric_of_lt_one hy0 hylt1, div_eq_mul_inv]
    have hn1 : (1:ℝ) ≤ ((n:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hden_pos : (0:ℝ) < ((n:ℝ)+1)^2 * (1 - lam^2) := by
      apply mul_pos (by linarith) (by linarith)
    have hyd_eq : y / (1 - y) = lam ^ 2 / (((n:ℝ)+1)^2 - lam ^ 2) := by
      rw [hy]
      have hden_ne : ((n:ℝ)+1)^2 ≠ 0 := by positivity
      field_simp
    have hdenom_le : ((n:ℝ)+1)^2 * (1 - lam^2) ≤ ((n:ℝ)+1)^2 - lam ^ 2 := by nlinarith
    have ha2 : (0:ℝ) < lam ^ 2 := by positivity
    have hc2 : (0:ℝ) < ((n:ℝ)+1)^2 - lam ^ 2 := by nlinarith
    calc ∑' k : ℕ, ‖term lam (n, k)‖
        = ∑' k : ℕ, y ^ (k + 1) / ((k:ℝ) + 1) := by simp only [heq]
      _ ≤ ∑' k : ℕ, y ^ (k + 1) := hrow_sum_summable.tsum_le_tsum hle hgeom_summable
      _ = y / (1 - y) := hgeom_eq
      _ = lam ^ 2 / (((n:ℝ)+1)^2 - lam ^ 2) := hyd_eq
      _ ≤ lam ^ 2 / (((n:ℝ)+1)^2 * (1 - lam^2)) :=
          (div_le_div_iff_of_pos_left ha2 hc2 hden_pos).mpr hdenom_le
  have hcol_summable : Summable (fun n : ℕ => lam ^ 2 / (((n:ℝ)+1)^2 * (1 - lam^2))) := by
    have h1mlam2 : (0:ℝ) < 1 - lam^2 := by linarith
    have hpseries : Summable (fun n : ℕ => 1 / ((n:ℝ)+1)^2) := by
      have h0 : Summable (fun n : ℕ => 1/(n:ℝ)^2) :=
        (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
      have h1 := (summable_nat_add_iff (f := fun n : ℕ => 1/(n:ℝ)^2) 1).mpr h0
      simpa using h1
    have heq2 : (fun n : ℕ => lam ^ 2 / (((n:ℝ)+1)^2 * (1 - lam^2)))
        = fun n : ℕ => (lam^2 / (1 - lam^2)) * (1 / ((n:ℝ)+1)^2) := by
      funext n; field_simp; ring
    rw [heq2]
    exact hpseries.mul_left _
  have hcol_bound_summable : Summable (fun n : ℕ => ∑' k : ℕ, ‖term lam (n, k)‖) :=
    Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun k => norm_nonneg _)) hrow_bound
      hcol_summable
  have hSnonneg : Summable (fun p : ℕ × ℕ => ‖term lam p‖) :=
    (summable_prod_of_nonneg (fun p => norm_nonneg (term lam p))).mpr
      ⟨hrow_summable, hcol_bound_summable⟩
  exact hSnonneg.of_norm

/-- **The cumulant law's double-indexed core**: the unconditional sum, over all `(n,k)`, of
`(-1)^k(λ²/(n+1)²)^{k+1}/(k+1)` equals `log(sinh(πλ)/(πλ)) = -log(P λ)`. -/
theorem hasSum_log_double (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    HasSum (term lam) (Real.log (Real.sinh (Real.pi * lam) / (Real.pi * lam))) := by
  have hS := summable_double lam hlam0 hlam1
  obtain ⟨a, ha⟩ := hS
  have hfiber := ha.prod_fiberwise (hasSum_row lam hlam0 hlam1)
  have hrow := GppSinhLogSeries.hasSum_log_one_add_sq_div hlam0.ne'
  have := hfiber.unique hrow
  rwa [this] at ha

end GppCumulantLaw
