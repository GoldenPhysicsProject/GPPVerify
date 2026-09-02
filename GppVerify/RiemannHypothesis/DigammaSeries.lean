import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# The Gauss series for the digamma function: what is provable, and what is not

`SpectralWeil.lean` parks the claim

    `Γ'/Γ(s) = -γ - 1/s + ∑_{n ≥ 1} (1/n - 1/(n+s))`

as `open_digamma_series_form`. This module proves everything about that series that does not
require identifying it with `ψ`, and states precisely what the identification still needs.

## What is proved here, unconditionally

* `digammaSeriesTerm_eq` — the term is `s / ((n+1)(n+1+s))`, hence `O(1/n²)`.
* `summable_digammaSeriesTerm` — the series converges absolutely for every `s` off the
  non-positive integers.
* `digammaSeries_one` — at `s = 1` the series telescopes and `digammaSeries 1 = -γ`. That is
  exactly Mathlib's `Complex.digamma_one`, which Mathlib proves from the derivative of `Gamma`
  at `1` — a route with nothing to do with this series. So this is a real check of the formula
  at a point, not a restatement of it.
* `digammaSeries_add_one` — the series satisfies `F (s+1) = F s + 1/s`, which is exactly the
  functional equation `Complex.digamma_apply_add_one` proves for `ψ`.

## What is NOT proved here, and why the stub stays

`digammaSeries = Complex.digamma` does **not** follow from the above. Their difference is a
`1`-periodic function vanishing at `1`; killing it needs a growth or convexity input
(Wielandt / Bohr–Mollerup-style uniqueness), not another functional-equation manipulation.

Mathlib 4.33.1 has `Complex.digamma` with `digamma_zero`, `digamma_one`, `digamma_one_half`,
`digamma_apply_add_one` and `meromorphic_digamma`, and its own module header lists Gauss'
representation under `TODO`. So the identification is a **LIBRARY GAP**, and
`open_digamma_series_form` stays until it closes.

Worth being exact about the size of what is left, because the stub's docstring reads as if the
whole series were open. Convergence and the functional equation are where a formalization of a
series identity normally spends its effort, and both are done here. What remains is the
uniqueness step alone.
-/

namespace GppDigammaSeries

open Complex Filter Finset

/-- The `n`-th term of the Gauss series, indexed from `0`, so `n` here is the classical
statement's `n+1`: `1/(n+1) - 1/(n+1+s)`. -/
noncomputable def digammaSeriesTerm (s : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + 1)⁻¹ - ((n : ℂ) + 1 + s)⁻¹

/-- The Gauss series itself, as a candidate for `ψ`. -/
noncomputable def digammaSeries (s : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) - s⁻¹ + ∑' n : ℕ, digammaSeriesTerm s n

/-- `s` avoids the poles of the series: `n + 1 + s ≠ 0` for every `n`. Equivalently, `s` is not
a negative integer. -/
def OffPoles (s : ℂ) : Prop := ∀ n : ℕ, (n : ℂ) + 1 + s ≠ 0

theorem natCast_add_one_ne_zero (n : ℕ) : ((n : ℂ) + 1) ≠ 0 := by
  have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [h]
  exact_mod_cast Nat.succ_ne_zero n

theorem offPoles_one : OffPoles 1 := by
  intro n
  have h : ((n : ℂ) + 1 + 1) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
  rw [h]
  exact_mod_cast Nat.succ_ne_zero (n + 1)

theorem offPoles_add_one {s : ℂ} (hs : OffPoles s) : OffPoles (s + 1) := by
  intro n
  have h := hs (n + 1)
  have e : ((n : ℂ) + 1 + (s + 1)) = (((n + 1 : ℕ) : ℂ) + 1 + s) := by push_cast; ring
  rw [e]
  exact h

/-- Combining the two fractions: the term is `s / ((n+1)(n+1+s))`, which makes both its size
and its vanishing at `s = 0` visible. -/
theorem digammaSeriesTerm_eq {s : ℂ} {n : ℕ} (h : (n : ℂ) + 1 + s ≠ 0) :
    digammaSeriesTerm s n = s / (((n : ℂ) + 1) * ((n : ℂ) + 1 + s)) := by
  have hn : ((n : ℂ) + 1) ≠ 0 := natCast_add_one_ne_zero n
  simp only [digammaSeriesTerm]
  field_simp
  ring

/-! ### Convergence -/

/-- `‖(n : ℂ) + c‖ → ∞`: a fixed shift cannot beat the growth of `n`. -/
theorem tendsto_norm_natCast_add_atTop (c : ℂ) :
    Tendsto (fun n : ℕ => ‖(n : ℂ) + c‖) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) (tendsto_atTop_add_const_right _ (-‖c‖)
    (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h : ‖(n : ℂ)‖ ≤ ‖(n : ℂ) + c‖ + ‖c‖ := by
    simpa using norm_sub_le ((n : ℂ) + c) c
  have hn : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  rw [hn] at h
  linarith

/-- `((n : ℂ) + c)⁻¹ → 0`. -/
theorem tendsto_inv_natCast_add (c : ℂ) :
    Tendsto (fun n : ℕ => ((n : ℂ) + c)⁻¹) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  exact (tendsto_norm_natCast_add_atTop c).inv_tendsto_atTop

theorem norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [h, _root_.norm_natCast]
  push_cast
  ring

/-- **The series converges absolutely away from the poles.** Unconditional: this is the part of
`open_digamma_series_form` that needs no library gap at all. -/
theorem summable_digammaSeriesTerm {s : ℂ} (hs : OffPoles s) :
    Summable (digammaSeriesTerm s) := by
  have hsq : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    simpa using h
  refine Summable.of_norm_bounded_eventually_nat (hsq.mul_left (2 * ‖s‖)) ?_
  -- Once `n ≥ 2‖s‖` we have `‖n+1+s‖ ≥ (n+1)/2`, so `‖term‖ ≤ 2‖s‖/(n+1)²`.
  filter_upwards [eventually_ge_atTop (⌈2 * ‖s‖⌉₊)] with n hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hbig : 2 * ‖s‖ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hlow : ((n : ℝ) + 1) / 2 ≤ ‖(n : ℂ) + 1 + s‖ := by
    have h : ‖(n : ℂ) + 1‖ ≤ ‖(n : ℂ) + 1 + s‖ + ‖s‖ := by
      simpa using norm_sub_le ((n : ℂ) + 1 + s) s
    rw [norm_natCast_add_one] at h
    linarith
  have hnum : ‖digammaSeriesTerm s n‖ = ‖s‖ / (((n : ℝ) + 1) * ‖(n : ℂ) + 1 + s‖) := by
    rw [digammaSeriesTerm_eq (hs n), norm_div, norm_mul, norm_natCast_add_one]
  have hrhs : 2 * ‖s‖ * (1 / ((n : ℝ) + 1) ^ 2)
      = ‖s‖ / (((n : ℝ) + 1) * (((n : ℝ) + 1) / 2)) := by
    field_simp
  rw [hnum, hrhs]
  -- `gcongr` reduces to the denominator comparison and closes it from `hlow` in context.
  gcongr

/-! ### Telescoping -/

/-- A telescoping series with vanishing tail sums to its first term. Both concrete results
below are instances; they differ only in which `f` they telescope. -/
theorem hasSum_telescope {f : ℕ → ℂ} (h0 : Tendsto f atTop (nhds 0))
    (hsum : Summable fun n => f n - f (n + 1)) :
    HasSum (fun n => f n - f (n + 1)) (f 0) := by
  rw [hsum.hasSum_iff_tendsto_nat]
  have hpartial : ∀ N : ℕ, (∑ i ∈ range N, (f i - f (i + 1))) = f 0 - f N :=
    fun N => Finset.sum_range_sub' f N
  simp only [hpartial]
  have hconst : Tendsto (fun _ : ℕ => f 0) atTop (nhds (f 0)) := tendsto_const_nhds
  simpa using hconst.sub h0

/-- At `s = 1` the series telescopes: `∑ (1/(n+1) - 1/(n+2)) = 1`. -/
theorem hasSum_digammaSeriesTerm_one : HasSum (digammaSeriesTerm 1) 1 := by
  have hdiff : ∀ n : ℕ,
      digammaSeriesTerm 1 n = ((n : ℂ) + 1)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1)⁻¹ := by
    intro n
    have e : ((n : ℂ) + 1 + 1) = (((n + 1 : ℕ) : ℂ) + 1) := by push_cast; ring
    simp only [digammaSeriesTerm, e]
  have hsum : Summable fun n : ℕ => ((n : ℂ) + 1)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1)⁻¹ :=
    (summable_digammaSeriesTerm offPoles_one).congr hdiff
  have h := hasSum_telescope (f := fun n : ℕ => ((n : ℂ) + 1)⁻¹)
    (by simpa using tendsto_inv_natCast_add 1) hsum
  have heq : (fun n : ℕ => ((n : ℂ) + 1)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1)⁻¹) = digammaSeriesTerm 1 :=
    funext fun n => (hdiff n).symm
  rw [heq] at h
  simpa using h

/-- **The formula, checked at a point.** `digammaSeries 1 = -γ`, which is
`Complex.digamma_one` — proved in Mathlib from the derivative of `Gamma` at `1`, by a route
that has nothing to do with this series. -/
theorem digammaSeries_one : digammaSeries 1 = Complex.digamma 1 := by
  rw [digammaSeries, hasSum_digammaSeriesTerm_one.tsum_eq, Complex.digamma_one]
  ring

/-! ### The functional equation -/

/-- **The series obeys `ψ`'s functional equation:** `F (s+1) = F s + 1/s`, matching
`Complex.digamma_apply_add_one`.

No `s ≠ 0` hypothesis: the `s⁻¹` terms cancel formally, and Lean's `0⁻¹ = 0` makes the
statement true at `s = 0` too. Carrying the hypothesis would suggest the identity depends on
it. -/
theorem digammaSeries_add_one {s : ℂ} (hs : OffPoles s) :
    digammaSeries (s + 1) = digammaSeries s + s⁻¹ := by
  have hdiff : ∀ n : ℕ, digammaSeriesTerm (s + 1) n - digammaSeriesTerm s n
      = ((n : ℂ) + 1 + s)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1 + s)⁻¹ := by
    intro n
    have e : ((n : ℂ) + 1 + (s + 1)) = (((n + 1 : ℕ) : ℂ) + 1 + s) := by push_cast; ring
    simp only [digammaSeriesTerm, e]
    ring
  have hsum1 : Summable (digammaSeriesTerm (s + 1)) :=
    summable_digammaSeriesTerm (offPoles_add_one hs)
  have hsum0 : Summable (digammaSeriesTerm s) := summable_digammaSeriesTerm hs
  have hsumd : Summable fun n : ℕ => ((n : ℂ) + 1 + s)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1 + s)⁻¹ :=
    (hsum1.sub hsum0).congr hdiff
  have htel := hasSum_telescope (f := fun n : ℕ => ((n : ℂ) + 1 + s)⁻¹)
    (by simpa [add_assoc] using tendsto_inv_natCast_add (1 + s)) hsumd
  have hkey : (∑' n, digammaSeriesTerm (s + 1) n) - (∑' n, digammaSeriesTerm s n)
      = (s + 1)⁻¹ := by
    rw [← hsum1.tsum_sub hsum0, tsum_congr hdiff, htel.tsum_eq]
    simp only [Nat.cast_zero, zero_add]
    rw [add_comm (1 : ℂ) s]
  simp only [digammaSeries]
  linear_combination hkey

end GppDigammaSeries
