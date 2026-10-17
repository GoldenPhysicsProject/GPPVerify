import GppVerify.RiemannHypothesis.CramerIntensityBound
import GppVerify.NumberTheory.MertensFirst

/-!
# No fixed intensity budget for independently charged prime-power channels

Source: Codex/GPP, `work/codex/2026-10-16_independent_prime_Poisson_KL_intensity_budget_no_go.md`
(PR11 comment 6216029557), in the setting of Astra's gamma-free Poisson transport.

Each prime-power channel `n` with reference intensity `α n > 0`, tilted mean `w = Λ(n)/√n` and entropy
budget `w · log n` obeys the Cramér inequality `rate (α n) w ≤ w · log n`. `GppCramerIntensityBound`
turned that into the local bound `α n ≥ (2/e) Λ(n)/n`; here Mertens' first theorem
(`GppMertens.mertens_first`) sums it:

* `intensity_sum_lower`: `(2/e)(log N − 1) ≤ Σ_{n ≤ N} α n`;
* `no_fixed_intensity_budget`: for every bound `B` some cutoff `N` has `Σ_{n ≤ N} α n > B`, in particular
  no fixed reference intensity (Astra's budget is `4`) can host all channels.

**Scope, stated plainly.** The Cramér inequality is a *hypothesis* (that every law with mean `w` has
relative entropy at least `rate α w` is a probability fact not formalized here). The result concerns
independent channels each charged its own entropy budget; Codex's note is explicit that it does *not*
cover correlated constructions, globally compensated entropy sharing, or KMS/CFS/signed completions,
and it is not a statement about RH. No RH claim.
-/

namespace GppIndependentChannelBudgetNoGo

open ArithmeticFunction Finset GppCramerIntensityBound GppMertens Real

/-- Channelwise: `α n ≥ (2/e) Λ(n)/n` for every `n ≥ 1`. -/
theorem alpha_ge (α : ℕ → ℝ) (hα : ∀ n, 0 < α n)
    (hrate : ∀ n, 0 < Λ n → rate (α n) (Λ n / √(n : ℝ)) ≤ Λ n / √(n : ℝ) * Real.log n)
    (n : ℕ) : 2 / Real.exp 1 * (Λ n / n) ≤ α n := by
  rcases (vonMangoldt_nonneg (n := n)).eq_or_lt with h0 | hpos
  · rw [← h0]; simp [(hα n).le]
  · have hn : (1 : ℝ) < n := by
      have : 1 < n := by
        rcases Nat.lt_or_ge 1 n with h | h
        · exact h
        · interval_cases n <;> simp_all
      exact_mod_cast this
    exact alpha_lower_prime_power (hα n) hn hpos (hrate n hpos)

/-- `(2/e)(log N − 1) ≤ Σ_{n ≤ N} α n`. -/
theorem intensity_sum_lower (α : ℕ → ℝ) (hα : ∀ n, 0 < α n)
    (hrate : ∀ n, 0 < Λ n → rate (α n) (Λ n / √(n : ℝ)) ≤ Λ n / √(n : ℝ) * Real.log n)
    (N : ℕ) (hN : 1 ≤ N) :
    2 / Real.exp 1 * (Real.log N - 1) ≤ ∑ n ∈ Ioc 0 N, α n := by
  have hmert := mertens_first_lower N hN
  have hexp : 0 < 2 / Real.exp 1 := by positivity
  calc 2 / Real.exp 1 * (Real.log N - 1)
      ≤ 2 / Real.exp 1 * ∑ d ∈ Ioc 0 N, Λ d / d := mul_le_mul_of_nonneg_left hmert hexp.le
    _ = ∑ d ∈ Ioc 0 N, 2 / Real.exp 1 * (Λ d / d) := by rw [Finset.mul_sum]
    _ ≤ ∑ n ∈ Ioc 0 N, α n := Finset.sum_le_sum fun n _ => alpha_ge α hα hrate n

/-- **No fixed budget**: the cumulative intensity is unbounded. -/
theorem no_fixed_intensity_budget (α : ℕ → ℝ) (hα : ∀ n, 0 < α n)
    (hrate : ∀ n, 0 < Λ n → rate (α n) (Λ n / √(n : ℝ)) ≤ Λ n / √(n : ℝ) * Real.log n)
    (B : ℝ) : ∃ N : ℕ, 1 ≤ N ∧ B < ∑ n ∈ Ioc 0 N, α n := by
  obtain ⟨N, hN, hS⟩ := sum_vonMangoldt_div_unbounded (B * Real.exp 1 / 2)
  refine ⟨N, hN, ?_⟩
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  have hlow : 2 / Real.exp 1 * ∑ d ∈ Ioc 0 N, Λ d / d ≤ ∑ n ∈ Ioc 0 N, α n := by
    calc 2 / Real.exp 1 * ∑ d ∈ Ioc 0 N, Λ d / d
        = ∑ d ∈ Ioc 0 N, 2 / Real.exp 1 * (Λ d / d) := by rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun n _ => alpha_ge α hα hrate n
  have : B < 2 / Real.exp 1 * ∑ d ∈ Ioc 0 N, Λ d / d := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hexp]
    nlinarith [hS]
  linarith

/-- In particular the reference budget `4` of Astra's Poisson construction is eventually exceeded. -/
theorem budget_four_exceeded (α : ℕ → ℝ) (hα : ∀ n, 0 < α n)
    (hrate : ∀ n, 0 < Λ n → rate (α n) (Λ n / √(n : ℝ)) ≤ Λ n / √(n : ℝ) * Real.log n) :
    ¬ ∀ N : ℕ, ∑ n ∈ Ioc 0 N, α n ≤ 4 := by
  intro h
  obtain ⟨N, _, hN⟩ := no_fixed_intensity_budget α hα hrate 4
  exact absurd (h N) (not_le.mpr hN)

end GppIndependentChannelBudgetNoGo
