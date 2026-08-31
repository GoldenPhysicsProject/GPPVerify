import GppVerify.QuantumGravity.SinhWeierstrassProduct
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The log of the sinh Weierstrass product, as a genuine `HasSum`

From `Modular_Thermality_of_the_Celestial_Spectral_Weight.tex` / `blackbody_law_qg_dtoupin_v1.tex`,
Proposition "Equivalent descriptions" item (v) / "Six faces", the cumulant law:
`log P(λ) = -Σ_{k≥1} (-1)^{k+1} ζ(2k) λ^{2k}/k` for `|λ| < 1`. `docs/FORMALIZATION_PLAN.md`
flags this as the natural next target once `SinhWeierstrassProduct.lean` landed ("no longer
blocked on a missing special function"): taking `log` of the Weierstrass product and expanding
`log(1+x)` termwise, then swapping the sum over `n` and the sum over `k`.

## What this file proves

The first (log-of-product) half of that chain, as a genuine `HasSum` rather than a numerical
check: for `λ ≠ 0`,
```
HasSum (fun n : ℕ => Real.log (1 + λ²/(n+1)²)) (Real.log (sinh(πλ)/(πλ)))
```
i.e. `Real.log(sinh(πλ)/(πλ)) = Σ_{n≥0} log(1+λ²/(n+1)²)` — the *unconditional* infinite sum
of logs, not a numerically-truncated approximation. Since `sinh(πλ)/(πλ) = (P λ)⁻¹`, this is
`-log(P λ) = Σ log(1+λ²/(n+1)²)`, the exact starting point of the cumulant law's proof.

**Proof shape**: `SinhWeierstrassProduct.tendsto_prod_one_add_sq_div` gives the partial
*products* converging to `sinh(πλ)`; dividing by the nonzero constant `πλ` and applying
`Real.log` (continuous at the positive limit `sinh(πλ)/(πλ)`, proved positive here from
`Real.sinh_lt_sinh`'s strict monotonicity rather than assumed) turns this into convergence of
the partial *sums* of `Real.log_prod`-expanded logs; since every term is nonnegative
(`Real.log_nonneg`, as `1 + λ²/(n+1)² ≥ 1`), `hasSum_iff_tendsto_nat_of_nonneg` upgrades that
convergence to a genuine `HasSum`.

## What this file does NOT do

The remaining two steps of the cumulant law's own proof — expanding each `log(1+λ²/(n+1)²)`
into its own power series `Σ_k (-1)^{k+1}(λ²/(n+1)²)^k/k` (needs Mathlib's `log(1+x)` series,
valid for `|x|<1`) and swapping the resulting double sum over `n` and `k` (needs an absolute-
summability estimate for `|λ|<1`) — are not attempted here; this file supplies exactly the
piece that was missing before (the log-of-an-infinite-product step), left as the honestly
scoped next step. No axiom, no sorry.
-/

namespace GppSinhLogSeries

open Filter Topology

/-- `sinh(x)` has the same strict sign as `x`: `0 < x → 0 < sinh x`, from `sinh`'s strict
monotonicity (`Real.sinh_lt_sinh`) and `sinh 0 = 0`. -/
theorem sinh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x := by
  have h := Real.sinh_lt_sinh.mpr hx
  rwa [Real.sinh_zero] at h

/-- `0 < sinh(πλ)/(πλ)` for every `λ ≠ 0`: both numerator and denominator have the same
sign as `λ`. -/
theorem sinh_div_pos {lam : ℝ} (hlam : lam ≠ 0) :
    0 < Real.sinh (Real.pi * lam) / (Real.pi * lam) := by
  rcases hlam.lt_or_gt with hneg | hpos
  · have h1 : Real.pi * lam < 0 := mul_neg_of_pos_of_neg Real.pi_pos hneg
    have h2 : Real.sinh (Real.pi * lam) < 0 := by
      have := sinh_pos_of_pos (x := -(Real.pi * lam)) (by linarith)
      rwa [Real.sinh_neg, neg_pos] at this
    exact div_pos_of_neg_of_neg h2 h1
  · have h1 : 0 < Real.pi * lam := mul_pos Real.pi_pos hpos
    exact div_pos (sinh_pos_of_pos h1) h1

/-- **The log of the Weierstrass product, as a genuine `HasSum`.** For `λ ≠ 0`,
`Σ_{n≥0} log(1+λ²/(n+1)²) = log(sinh(πλ)/(πλ))` unconditionally. -/
theorem hasSum_log_one_add_sq_div {lam : ℝ} (hlam : lam ≠ 0) :
    HasSum (fun n : ℕ => Real.log (1 + lam ^ 2 / ((n : ℝ) + 1) ^ 2))
      (Real.log (Real.sinh (Real.pi * lam) / (Real.pi * lam))) := by
  have hpilam : Real.pi * lam ≠ 0 := mul_ne_zero Real.pi_ne_zero hlam
  have hprod : Tendsto (fun n : ℕ =>
      ∏ j ∈ Finset.range n, ((1 : ℝ) + lam ^ 2 / ((j : ℝ) + 1) ^ 2)) atTop
      (𝓝 (Real.sinh (Real.pi * lam) / (Real.pi * lam))) := by
    have h := (GppSinhWeierstrass.tendsto_prod_one_add_sq_div lam).div_const (Real.pi * lam)
    have heq : (fun n : ℕ => Real.pi * lam *
        (∏ j ∈ Finset.range n, ((1 : ℝ) + lam ^ 2 / ((j : ℝ) + 1) ^ 2)) / (Real.pi * lam))
        = (fun n : ℕ => ∏ j ∈ Finset.range n, ((1 : ℝ) + lam ^ 2 / ((j : ℝ) + 1) ^ 2)) := by
      funext n
      field_simp
      ring
    rwa [heq] at h
  have hterm_pos : ∀ n : ℕ, (0 : ℝ) < 1 + lam ^ 2 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    have : (0:ℝ) ≤ lam ^ 2 / ((n : ℝ) + 1) ^ 2 := by positivity
    linarith
  have hterm_ne : ∀ n : ℕ, (1 : ℝ) + lam ^ 2 / ((n : ℝ) + 1) ^ 2 ≠ 0 :=
    fun n => (hterm_pos n).ne'
  have hlog_prod : ∀ n : ℕ,
      Real.log (∏ j ∈ Finset.range n, ((1 : ℝ) + lam ^ 2 / ((j : ℝ) + 1) ^ 2))
        = ∑ j ∈ Finset.range n, Real.log (1 + lam ^ 2 / ((j : ℝ) + 1) ^ 2) :=
    fun n => Real.log_prod _ _ (fun j _ => hterm_ne j)
  have hpos_lim : 0 < Real.sinh (Real.pi * lam) / (Real.pi * lam) := sinh_div_pos hlam
  have hlogtendsto : Tendsto (fun n : ℕ =>
      ∑ j ∈ Finset.range n, Real.log (1 + lam ^ 2 / ((j : ℝ) + 1) ^ 2)) atTop
      (𝓝 (Real.log (Real.sinh (Real.pi * lam) / (Real.pi * lam)))) := by
    have hcomp := (Real.continuousAt_log hpos_lim.ne').tendsto.comp hprod
    have heq2 : (Real.log ∘ fun n : ℕ =>
        ∏ j ∈ Finset.range n, ((1 : ℝ) + lam ^ 2 / ((j : ℝ) + 1) ^ 2))
        = (fun n : ℕ => ∑ j ∈ Finset.range n, Real.log (1 + lam ^ 2 / ((j : ℝ) + 1) ^ 2)) := by
      funext n
      exact hlog_prod n
    rwa [heq2] at hcomp
  have hnonneg : ∀ n : ℕ, 0 ≤ Real.log (1 + lam ^ 2 / ((n : ℝ) + 1) ^ 2) := by
    intro n
    apply Real.log_nonneg
    have hge : (0 : ℝ) ≤ lam ^ 2 / ((n : ℝ) + 1) ^ 2 := by positivity
    linarith
  exact (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).mpr hlogtendsto

end GppSinhLogSeries
