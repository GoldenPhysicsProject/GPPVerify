import GppVerify.QuantumGravity.CumulantLaw

/-!
# The cumulant law, regrouped into its single-index closed form

`CumulantLaw.lean` proved the double-indexed core of the cumulant law
(`log P(λ)... `; more precisely `log(sinh(πλ)/(πλ))`) and flagged the single remaining step
as "a `tsum_prod'`/reindexing exercise" grouping the double sum by `k` alone. This file
does that regrouping, landing the paper's own literal single-index statement (up to the
harmless index shift `k ↦ k+1` — `CumulantLaw.lean`'s inner index `k` runs from `0`, so the
`k`-th term there carries exponent `k+1`; grouping "by `k`" here therefore naturally
produces a sum indexed by `m := k+1 ≥ 1`, exactly the paper's own convention).

## What this file proves

Write `zetaR p := Σ'_{n≥0} 1/(n+1)^p` for the literal Dirichlet-series definition of `ζ(p)`
(no need to import or identify Mathlib's `riemannZeta` — the double sum already lands
exactly on this object by definition, so importing a separate named zeta function would add
an identification step with no further content). Then, for `0 < λ < 1`,
```
HasSum (fun k : ℕ => (-1)^k * λ^(2*(k+1)) * zetaR (2*(k+1)) / (k+1))
  (log (sinh(πλ)/(πλ)))
```
i.e. `log(sinh(πλ)/(πλ)) = Σ_{k≥0} (-1)^k ζ(2k+2) λ^{2k+2}/(k+1)`, which is the paper's
`log P(λ) = -Σ_{m≥1}(-1)^{m+1}ζ(2m)λ^{2m}/m` with `m=k+1` (both sides equal
`-log P(λ) = log(sinh(πλ)/(πλ))`, and `(-1)^k = (-1)^{m-1} = (-1)^{m+1}`).

**Proof**: swap the roles of the two indices in `CumulantLaw.summable_double`'s already-
established `Summable (term lam)` via `Equiv.prodComm` and `HasSum.prod_fiberwise`, using a
fresh per-`k`-row computation (`hasSum_row_by_k`, the geometric-in-`n` sum
`Σ'_n (λ²/(n+1)²)^{k+1} = λ^{2(k+1)}·ζ(2(k+1))`, an ordinary shifted `p`-series with
`p = 2(k+1) ≥ 2 > 1`) in place of `CumulantLaw.hasSum_row`'s per-`n`-row computation. No
axiom, no sorry.
-/

namespace GppCumulantLawClosedForm

open Filter Topology GppCumulantLaw

/-- The literal Dirichlet-series definition of `ζ(p)` used here, avoiding any need to
import or identify Mathlib's `riemannZeta`. -/
noncomputable def zetaR (p : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ p

/-- `Σ'_n 1/(n+1)^p` is summable for `p ≥ 2`, by the standard shift of the `p`-series. -/
theorem summable_zetaR_term {p : ℕ} (hp : 1 < p) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ p) := by
  have h0 : Summable (fun n : ℕ => 1 / (n:ℝ) ^ p) := (Real.summable_one_div_nat_pow (p := p)).mpr hp
  have h1 := (summable_nat_add_iff (f := fun n : ℕ => 1/(n:ℝ)^p) 1).mpr h0
  simpa using h1

/-- **Per-`k`-row computation**: for fixed `k`, the `n`-indexed row of `term lam` sums to
`(-1)^k·λ^{2(k+1)}·ζ(2(k+1))/(k+1)`. -/
theorem hasSum_row_by_k (lam : ℝ) (hlam0 : 0 < lam) (k : ℕ) :
    HasSum (fun n : ℕ => term lam (n, k))
      ((-1 : ℝ) ^ k * lam ^ (2 * (k + 1)) * zetaR (2 * (k + 1)) / ((k : ℝ) + 1)) := by
  have hp : 1 < 2 * (k + 1) := by omega
  have hS := summable_zetaR_term hp
  have hHS : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * (k + 1))) (zetaR (2 * (k + 1))) :=
    hS.hasSum
  have hmul := hHS.mul_left (lam ^ (2 * (k + 1)))
  have heq1 : ∀ n : ℕ, lam ^ (2 * (k + 1)) * (1 / ((n : ℝ) + 1) ^ (2 * (k + 1)))
      = (lam ^ 2 / ((n : ℝ) + 1) ^ 2) ^ (k + 1) := by
    intro n
    rw [div_pow, pow_mul, pow_mul]
    ring
  simp only [heq1] at hmul
  have hmul2 := hmul.mul_left ((-1 : ℝ) ^ k)
  have hmul3 := hmul2.div_const ((k : ℝ) + 1)
  have hassoc : (-1 : ℝ) ^ k * (lam ^ (2 * (k + 1)) * zetaR (2 * (k + 1))) / ((k : ℝ) + 1)
      = (-1 : ℝ) ^ k * lam ^ (2 * (k + 1)) * zetaR (2 * (k + 1)) / ((k : ℝ) + 1) := by ring
  rw [hassoc] at hmul3
  have heq2 : ∀ n : ℕ, (-1 : ℝ) ^ k * (lam ^ 2 / ((n : ℝ) + 1) ^ 2) ^ (k + 1) / ((k : ℝ) + 1)
      = term lam (n, k) := by
    intro n
    simp only [term]
  simpa only [heq2] using hmul3

/-- **The cumulant law, single-index closed form**: for `0 < λ < 1`,
`log(sinh(πλ)/(πλ)) = Σ_{k≥0} (-1)^k ζ(2k+2) λ^{2k+2}/(k+1)`. -/
theorem hasSum_cumulant_closed_form (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k * lam ^ (2 * (k + 1)) * zetaR (2 * (k + 1)) / ((k : ℝ) + 1))
      (Real.log (Real.sinh (Real.pi * lam) / (Real.pi * lam))) := by
  have hrow : HasSum (term lam) (Real.log (Real.sinh (Real.pi * lam) / (Real.pi * lam))) :=
    hasSum_log_double lam hlam0 hlam1
  have hswapped : HasSum (fun q : ℕ × ℕ => term lam (q.2, q.1))
      (Real.log (Real.sinh (Real.pi * lam) / (Real.pi * lam))) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hrow
  exact hswapped.prod_fiberwise (fun k => hasSum_row_by_k lam hlam0 k)

end GppCumulantLawClosedForm
