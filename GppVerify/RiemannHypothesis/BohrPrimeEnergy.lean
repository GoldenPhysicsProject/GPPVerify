import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bohr prime energy: ζ is finite above `½`, `F_θ` only above `½ + θ`

Source: Codex, GPPDiscovery2 `research/codex/2026-10-08_bohr_prime_energy_bound_and_evaluation_obstruction.md`
§§1–2 (the Bohr mean-square energy of the von Mangoldt current).

The Bohr–Parseval energy of `J_σ(t) = Σ Λ(n) n^{−σ} e^{−it log n}` is `B(σ) = Σ Λ(n)² n^{−2σ}`.
* `summable_iff`: **`B(σ) < ∞` iff `σ > ½`.** The `⇐` direction uses `Λ(n) ≤ log n ≤ n^ε/ε`. The `⇒`
  direction compares with `Σ_p 1/p = ∞` (Mathlib's `not_summable_one_div_on_primes`).
* For `F_θ(s) = ξ(s−θ)ξ(s+θ)` the logarithmic prime coefficients are `Λ_θ(n) = Λ(n)(n^θ + n^{−θ})`.
  - `thetaTerm_eq`: `Λ_θ(n)² n^{−2σ} = B-term(σ−θ) + 2·B-term(σ) + B-term(σ+θ)`.
  - `summable_theta_iff`: **the `F_θ` energy is finite iff `σ > ½ + θ`** (for `θ ≥ 0`).

So on the strip `½ < σ ≤ ½ + θ` the ζ current has finite energy and the `F_θ` current does not.
This is a prime-side separation of `F_θ` from ζ that uses no zeros. It does **not** impose RH:
finiteness above `½` is a statement about absolute convergence, not about zeros. **No RH claim.**
-/

namespace GppBohrPrimeEnergy

open ArithmeticFunction Real

/-- The Bohr energy summand `Λ(n)² n^{−2u}`. -/
noncomputable def bterm (u : ℝ) (n : ℕ) : ℝ := Λ n ^ 2 * (n : ℝ) ^ (-2 * u)

lemma bterm_nonneg (u : ℝ) (n : ℕ) : 0 ≤ bterm u n := by
  unfold bterm; have := (n : ℝ).rpow_nonneg (Nat.cast_nonneg n) (-2 * u); positivity

/-- **`B(u) < ∞` iff `u > ½`.** -/
theorem summable_iff (u : ℝ) : Summable (bterm u) ↔ 1 / 2 < u := by
  constructor
  · intro hs
    by_contra hu
    push Not at hu
    apply not_summable_one_div_on_primes
    have hl2 : 0 < Real.log 2 ^ 2 := by have := Real.log_pos one_lt_two; positivity
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hs.div_const (Real.log 2 ^ 2))
    · by_cases hp : n ∈ {p : ℕ | p.Prime}
      · simp [Set.indicator_of_mem hp]
      · simp [Set.indicator_of_notMem hp]
    · by_cases hp : n ∈ {p : ℕ | p.Prime}
      · rw [Set.indicator_of_mem hp]
        have hpr : n.Prime := hp
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hpr.two_le
        have hn1 : (1 : ℝ) ≤ n := by linarith
        have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
        have hpow : (n : ℝ) ^ (-1 : ℝ) ≤ (n : ℝ) ^ (-2 * u) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        rw [le_div_iff₀ hl2]
        unfold bterm
        rw [vonMangoldt_apply_prime hpr]
        have hinv : (1 : ℝ) / n = (n : ℝ) ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one, one_div]
        rw [hinv]
        have h0 : 0 ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg (by linarith) _
        have hl0 : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
        calc (n : ℝ) ^ (-1 : ℝ) * Real.log 2 ^ 2 ≤ (n : ℝ) ^ (-2 * u) * Real.log n ^ 2 :=
              mul_le_mul hpow (pow_le_pow_left₀ hl0 hlog 2) (by positivity)
                (Real.rpow_nonneg (by linarith) _)
          _ = Real.log n ^ 2 * (n : ℝ) ^ (-2 * u) := mul_comm _ _
      · rw [Set.indicator_of_notMem hp]
        exact div_nonneg (bterm_nonneg u n) hl2.le
  · intro hu
    set ε := (2 * u - 1) / 4 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (2 * ε - 2 * u) / ε ^ 2) :=
      (summable_nat_rpow.mpr (by rw [hε]; linarith)).div_const _
    refine Summable.of_nonneg_of_le (bterm_nonneg u) (fun n => ?_) hsum
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hΛ0 : 0 ≤ Λ n := vonMangoldt_nonneg
    have hΛ : Λ n ≤ (n : ℝ) ^ ε / ε :=
      vonMangoldt_le_log.trans (Real.log_le_rpow_div hn0 hεpos)
    have hΛ2 : Λ n ^ 2 ≤ ((n : ℝ) ^ ε / ε) ^ 2 := pow_le_pow_left₀ hΛ0 hΛ 2
    unfold bterm
    rcases hn0.eq_or_lt with h | h
    · rw [← h, Real.zero_rpow (by linarith), Real.zero_rpow (by rw [hε]; linarith)]
      simp
    · calc Λ n ^ 2 * (n : ℝ) ^ (-2 * u) ≤ ((n : ℝ) ^ ε / ε) ^ 2 * (n : ℝ) ^ (-2 * u) :=
            mul_le_mul_of_nonneg_right hΛ2 (Real.rpow_nonneg hn0 _)
        _ = (n : ℝ) ^ (2 * ε - 2 * u) / ε ^ 2 := by
            rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hn0, div_mul_eq_mul_div,
              ← Real.rpow_add h]
            norm_num
            ring_nf

/-- The `F_θ` energy summand `Λ_θ(n)² n^{−2σ}`, `Λ_θ(n) = Λ(n)(n^θ + n^{−θ})`. -/
noncomputable def thetaTerm (θ σ : ℝ) (n : ℕ) : ℝ :=
  (Λ n * ((n : ℝ) ^ θ + (n : ℝ) ^ (-θ))) ^ 2 * (n : ℝ) ^ (-2 * σ)

/-- **The `F_θ` energy splits into three shifted ζ energies.** -/
theorem thetaTerm_eq (θ σ : ℝ) (n : ℕ) :
    thetaTerm θ σ n = bterm (σ - θ) n + 2 * bterm σ n + bterm (σ + θ) n := by
  unfold thetaTerm bterm
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn : (0 : ℝ) < n := by exact_mod_cast h
    have e1 : (n : ℝ) ^ θ * (n : ℝ) ^ θ * (n : ℝ) ^ (-2 * σ) = (n : ℝ) ^ (-2 * (σ - θ)) := by
      rw [← Real.rpow_add hn, ← Real.rpow_add hn]; ring_nf
    have e2 : (n : ℝ) ^ θ * (n : ℝ) ^ (-θ) = 1 := by
      rw [← Real.rpow_add hn]; simp
    have e3 : (n : ℝ) ^ (-θ) * (n : ℝ) ^ (-θ) * (n : ℝ) ^ (-2 * σ) =
        (n : ℝ) ^ (-2 * (σ + θ)) := by
      rw [← Real.rpow_add hn, ← Real.rpow_add hn]; ring_nf
    linear_combination Λ n ^ 2 * e1 + 2 * Λ n ^ 2 * (n : ℝ) ^ (-2 * σ) * e2 + Λ n ^ 2 * e3

/-- **The `F_θ` energy is finite iff `σ > ½ + θ`** (for `θ ≥ 0`). -/
theorem summable_theta_iff {θ : ℝ} (hθ : 0 ≤ θ) (σ : ℝ) :
    Summable (thetaTerm θ σ) ↔ 1 / 2 + θ < σ := by
  constructor
  · intro hs
    have : Summable (bterm (σ - θ)) := by
      refine Summable.of_nonneg_of_le (bterm_nonneg _) (fun n => ?_) hs
      rw [thetaTerm_eq]
      linarith [bterm_nonneg σ n, bterm_nonneg (σ + θ) n]
    have := (summable_iff _).mp this
    linarith
  · intro h
    have h1 := (summable_iff (σ - θ)).mpr (by linarith)
    have h2 := (summable_iff σ).mpr (by linarith)
    have h3 := (summable_iff (σ + θ)).mpr (by linarith)
    have := (h1.add (h2.mul_left 2)).add h3
    exact this.congr fun n => (thetaTerm_eq θ σ n).symm

/-- **The separation strip.** For `θ > 0` and `½ < σ ≤ ½ + θ`, the ζ energy is finite and the `F_θ`
energy is infinite. -/
theorem separation {θ σ : ℝ} (hθ : 0 < θ) (hσ : 1 / 2 < σ) (hσθ : σ ≤ 1 / 2 + θ) :
    Summable (bterm σ) ∧ ¬ Summable (thetaTerm θ σ) :=
  ⟨(summable_iff σ).mpr hσ, fun h => by linarith [(summable_theta_iff hθ.le σ).mp h]⟩

end GppBohrPrimeEnergy
