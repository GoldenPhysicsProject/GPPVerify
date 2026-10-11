import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-!
# Finite prime cutoffs cannot reproduce the Cayley–Laguerre coefficients

In the Cayley–Laguerre representation (Codex, 2026-10-11) the coefficients of
`H(z) = (ξ'/ξ)((2+z)/(1-z))` carry the prime-side sequence

  `E_n = Σ_m Λ(m) m⁻² L_n^{(-1)}(3 log m) − (3/2)(−2)ⁿ`,

where `L_n^{(-1)}(t) = [zⁿ] exp(−t z/(1−z))` and the `(−2)ⁿ` term is the pole
residue. Codex observed that any *finite* prime cutoff is swamped by the
residue: truncated sums grow at most like `(3/2)ⁿ`, while the residue grows
like `2ⁿ` with alternating sign.

This file proves a sharper, fully explicit version of the same statement.

* `lag n t` is the explicit coefficient
  `Σ_{k<n} C(n−1,k) (−t)^{k+1}/(k+1)!`, i.e. `L_n^{(-1)}(t)` for `n ≥ 1`
  (checked against the generating function in exact rationals; Mathlib has no
  Laguerre polynomials, so the identification is not itself a theorem here).
* `abs_lag_le`: `|lag n t| ≤ e^{n/4} e^{4t}` for `t ≥ 0`. This is elementary,
  via `C(n−1,k) ≤ n^{k+1}/(k+1)!` and splitting `(nt)^j/(j!)² ` as
  `((n/4)^j/j!)·((4t)^j/j!)`.
* `cutoff_sign`: for any finite family of weights `c_i` and nodes `t_i ≥ 0`
  with `Σ |c_i| e^{4 t_i} ≤ e^{n/4}`, the truncated sequence satisfies
  `(−1)ⁿ E_n ≤ e^{n/2} − (3/2)2ⁿ < 0`. So every truncated `E_n` has the residue's
  alternating sign, with exponentially growing size.
* `prime_cutoff_sign`: the prime case. With `c_m = Λ(m)/m²` and `t_m = 3 log m`
  on `2 ≤ m ≤ N`, any cutoff with `N¹² ≤ e^{n/4}` (that is, `N ≤ e^{n/48}`)
  gives `(−1)ⁿ E_{n,N} < 0`.
* `fixed_cutoff_eventually`: for each fixed finite family, this holds for all
  large `n`.

The prime cutoff and `n → ∞` do not commute. Matching the true `E_n` therefore
needs a cutoff at least exponential in `n`, and that is necessary, not
sufficient. This file says nothing about the zeros of `ξ`.

No RH claim.
-/

namespace GppNoGo.LaguerreCutoff

open Finset Real

/-- The explicit coefficient `[zⁿ] exp(−t z/(1−z))`, i.e. `L_n^{(-1)}(t)` for
`n ≥ 1` (and `0` at `n = 0`, where the generating-function constant term `1`
is not part of the prime sum's oscillating part). -/
noncomputable def lag (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ range n, ((n - 1).choose k : ℝ) * (-t) ^ (k + 1) / (k + 1).factorial

/-- The truncated prime-side sequence with weights `c` and nodes `t`. -/
noncomputable def E {ι : Type*} (s : Finset ι) (c t : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ s, c i * lag n (t i) - 3 / 2 * (-2 : ℝ) ^ n

lemma choose_le (n k : ℕ) (hk : k < n) :
    ((n - 1).choose k : ℝ) ≤ (n : ℝ) ^ (k + 1) / (k + 1).factorial := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : ((m + 1 - 1).choose k : ℝ) ≤ ((m + 1).choose (k + 1) : ℝ) := by
    rw [Nat.add_sub_cancel, Nat.choose_succ_succ]
    exact_mod_cast Nat.le_add_right _ _
  exact h1.trans (by simpa using Nat.choose_le_pow_div (α := ℝ) (k + 1) (m + 1))

/-- Elementary growth bound: `|L_n^{(-1)}(t)| ≤ e^{n/4} e^{4t}`. -/
theorem abs_lag_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |lag n t| ≤ exp (n / 4) * exp (4 * t) := by
  have hn : (0 : ℝ) ≤ n / 4 := by positivity
  have h4 : (0 : ℝ) ≤ 4 * t := by positivity
  calc |lag n t|
      ≤ ∑ k ∈ range n, |((n - 1).choose k : ℝ) * (-t) ^ (k + 1) / (k + 1).factorial| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range n, (n / 4 : ℝ) ^ (k + 1) / (k + 1).factorial * exp (4 * t) := by
        apply sum_le_sum
        intro k hk
        have hk' := mem_range.mp hk
        have hf : (0 : ℝ) < (k + 1).factorial := by positivity
        rw [abs_div, abs_mul, abs_pow, abs_neg, abs_of_nonneg ht, Nat.abs_cast,
          abs_of_pos hf]
        have hc := choose_le n k hk'
        have he := Real.pow_div_factorial_le_exp (4 * t) h4 (k + 1)
        calc ((n - 1).choose k : ℝ) * t ^ (k + 1) / (k + 1).factorial
            ≤ (n : ℝ) ^ (k + 1) / (k + 1).factorial * t ^ (k + 1) / (k + 1).factorial := by
              gcongr
          _ = (n / 4 : ℝ) ^ (k + 1) / (k + 1).factorial *
                ((4 * t) ^ (k + 1) / (k + 1).factorial) := by
              rw [div_pow, mul_pow]; field_simp
          _ ≤ (n / 4 : ℝ) ^ (k + 1) / (k + 1).factorial * exp (4 * t) := by
              gcongr
    _ = (∑ k ∈ range n, (n / 4 : ℝ) ^ (k + 1) / (k + 1).factorial) * exp (4 * t) := by
        rw [sum_mul]
    _ ≤ exp (n / 4) * exp (4 * t) := by
        gcongr
        calc ∑ k ∈ range n, (n / 4 : ℝ) ^ (k + 1) / (k + 1).factorial
            ≤ ∑ k ∈ range (n + 1), (n / 4 : ℝ) ^ k / k.factorial := by
              rw [sum_range_succ']; simp
          _ ≤ exp (n / 4) := Real.sum_le_exp_of_nonneg hn _

lemma exp_half_le (n : ℕ) : exp (n / 2) ≤ (2 : ℝ) ^ n := by
  have h : exp (1 / 2 : ℝ) ≤ 2 := by
    have h2 : exp (1 / 2 : ℝ) ^ 2 = exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ)]
  calc exp (n / 2) = exp (1 / 2) ^ n := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ 2 ^ n := pow_le_pow_left₀ (Real.exp_pos _).le h n

/-- **Cutoff sign theorem.** Whenever the truncation's total weight
`Σ |c_i| e^{4 t_i}` is at most `e^{n/4}`, the truncated `E_n` has sign `(−1)^{n+1}`
and size at least `(3/2)2ⁿ − e^{n/2}`. -/
theorem cutoff_bound {ι : Type*} (s : Finset ι) (c t : ι → ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) (n : ℕ)
    (hK : ∑ i ∈ s, |c i| * exp (4 * t i) ≤ exp (n / 4)) :
    (-1 : ℝ) ^ n * E s c t n ≤ exp (n / 2) - 3 / 2 * 2 ^ n := by
  have hS : |∑ i ∈ s, c i * lag n (t i)| ≤ exp (n / 2) := by
    calc |∑ i ∈ s, c i * lag n (t i)|
        ≤ ∑ i ∈ s, |c i| * (exp (n / 4) * exp (4 * t i)) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_lag_le n (ht i hi)) (abs_nonneg _)
      _ = exp (n / 4) * ∑ i ∈ s, |c i| * exp (4 * t i) := by
          rw [mul_sum]; refine sum_congr rfl fun i _ => by ring
      _ ≤ exp (n / 4) * exp (n / 4) := by gcongr
      _ = exp (n / 2) := by rw [← Real.exp_add]; ring_nf
  have hsgn : (-1 : ℝ) ^ n * (-2) ^ n = 2 ^ n := by
    rw [← mul_pow]; norm_num
  have hpm : |(-1 : ℝ) ^ n| = 1 := by simp
  have h1 : (-1 : ℝ) ^ n * ∑ i ∈ s, c i * lag n (t i) ≤ exp (n / 2) := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul, hpm, one_mul]; exact hS
  unfold E
  rw [mul_sub, show (-1 : ℝ) ^ n * (3 / 2 * (-2) ^ n) = 3 / 2 * ((-1) ^ n * (-2) ^ n) by ring,
    hsgn]
  linarith

theorem cutoff_sign {ι : Type*} (s : Finset ι) (c t : ι → ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) (n : ℕ)
    (hK : ∑ i ∈ s, |c i| * exp (4 * t i) ≤ exp (n / 4)) :
    (-1 : ℝ) ^ n * E s c t n < 0 := by
  have := cutoff_bound s c t ht n hK
  have h2 := exp_half_le n
  have : (0 : ℝ) < 2 ^ n := by positivity
  linarith

/-- For every fixed finite family, the sign `(−1)ⁿ E_n < 0` holds for all large `n`:
the truncated sequence never settles to the true `E_n`'s behaviour. -/
theorem fixed_cutoff_eventually {ι : Type*} (s : Finset ι) (c t : ι → ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) :
    ∀ᶠ n : ℕ in Filter.atTop, (-1 : ℝ) ^ n * E s c t n < 0 := by
  have hT : Filter.Tendsto (fun n : ℕ => exp ((n : ℝ) / 4)) Filter.atTop Filter.atTop :=
    tendsto_exp_atTop.comp
      (Filter.Tendsto.atTop_div_const (by norm_num) tendsto_natCast_atTop_atTop)
  filter_upwards [hT.eventually_ge_atTop (∑ i ∈ s, |c i| * exp (4 * t i))] with n hn
  exact cutoff_sign s c t ht n hn

open ArithmeticFunction in
/-- **Prime cutoff.** With weights `Λ(m)/m²` and nodes `3 log m` on `2 ≤ m ≤ N`,
every cutoff with `N¹² ≤ e^{n/4}` (equivalently `N ≤ e^{n/48}`) gives
`(−1)ⁿ E_{n,N} < 0`. So a cutoff with `log N = o(n)` can never match `E_n`. -/
theorem prime_cutoff_sign (N n : ℕ) (hN : (N : ℝ) ^ 12 ≤ exp (n / 4)) :
    (-1 : ℝ) ^ n *
      E (Icc 2 N) (fun m => (Λ m : ℝ) / (m : ℝ) ^ 2) (fun m => 3 * Real.log m) n < 0 := by
  apply cutoff_sign
  · intro m _; exact mul_nonneg (by norm_num) (Real.log_natCast_nonneg m)
  refine le_trans ?_ hN
  calc ∑ m ∈ Icc 2 N, |(Λ m : ℝ) / (m : ℝ) ^ 2| * exp (4 * (3 * Real.log m))
      ≤ ∑ m ∈ Icc 2 N, (N : ℝ) ^ 11 := by
        apply sum_le_sum
        intro m hm
        obtain ⟨h2, hmN⟩ := mem_Icc.mp hm
        have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
        have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
        have hexp : exp (4 * (3 * Real.log m)) = (m : ℝ) ^ 12 := by
          rw [show 4 * (3 * Real.log m) = ((12 : ℕ) : ℝ) * Real.log m by push_cast; ring,
            Real.exp_nat_mul, Real.exp_log hm0]
        have hΛ : (Λ m : ℝ) ≤ m := (vonMangoldt_le_log).trans
          ((Real.log_le_sub_one_of_pos hm0).trans (by linarith))
        rw [hexp, abs_of_nonneg (div_nonneg vonMangoldt_nonneg (by positivity))]
        calc (Λ m : ℝ) / (m : ℝ) ^ 2 * (m : ℝ) ^ 12 = (Λ m : ℝ) * (m : ℝ) ^ 10 := by
              field_simp
          _ ≤ (m : ℝ) * (m : ℝ) ^ 10 := by gcongr
          _ = (m : ℝ) ^ 11 := by ring
          _ ≤ (N : ℝ) ^ 11 := by gcongr
    _ ≤ (N : ℝ) ^ 12 := by
        rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
        have : ((N + 1 - 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N + 1 - 2 ≤ N)
        calc ((N + 1 - 2 : ℕ) : ℝ) * (N : ℝ) ^ 11 ≤ N * (N : ℝ) ^ 11 := by gcongr
          _ = (N : ℝ) ^ 12 := by ring

end GppNoGo.LaguerreCutoff
