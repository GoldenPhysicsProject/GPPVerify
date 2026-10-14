import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Divisors

/-!
# Hagedorn gap: the shifted control's prime gas has no Gibbs state on `1 < σ ≤ 1 + θ`

Source: Grok, GPP-bridge `work/grok/2026-10-14_prime_gas_unitarity.md` (PR #11 comment 6163398661);
numerics in GPPDiscovery5 `experiments/hagedorn_gap/`.

The Dirichlet part of the shifted control `F_θ = ξ(s − θ) ξ(s + θ)` is `ζ(s − θ) ζ(s + θ)`, whose
`n`-th coefficient is `a_θ(n) = Σ_{d ∣ n} d^θ (n/d)^{−θ}`. This file proves:
* `coeff_ge`: `a_θ(n) ≥ n^θ` for `n ≥ 1`, `θ ≥ 0` (the `d = n` term).
* `not_summable_gas`: for `σ ≤ 1 + θ`, `Σ_n a_θ(n) n^{−σ}` diverges. So the `F_θ` "prime gas" has
  Hagedorn point `σ_H ≥ 1 + θ`. ζ's gas converges for every `σ > 1` (`PrimeFockPartition`).

So the gap `σ_H − ½` is `½ + θ` for `F_θ` versus `½` for ζ. This is temperedness (`|α_p| ≤ 1`)
restated as gas stability. It is not a positivity statement. The Davenport–Heilbronn function has
bounded coefficients and `σ_H = 1`, so it passes this test: DH is caught by `Λ ≥ 0`
(`ShiftedFisherKernelNoGo`), not here. **No RH claim.**
-/

namespace GppHagedornGapShifted

open Real

/-- Coefficients of `ζ(s − θ) ζ(s + θ)`. -/
noncomputable def coeff (θ : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (d : ℝ) ^ θ * ((n / d : ℕ) : ℝ) ^ (-θ)

theorem coeff_ge {θ : ℝ} {n : ℕ} (hn : n ≠ 0) : (n : ℝ) ^ θ ≤ coeff θ n := by
  unfold coeff
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn
  have hterm : (n : ℝ) ^ θ * ((n / n : ℕ) : ℝ) ^ (-θ) = (n : ℝ) ^ θ := by
    rw [Nat.div_self (Nat.pos_of_ne_zero hn)]; simp
  rw [← hterm]
  exact Finset.single_le_sum (f := fun d : ℕ => (d : ℝ) ^ θ * ((n / d : ℕ) : ℝ) ^ (-θ))
    (fun d _ => mul_nonneg (rpow_nonneg (Nat.cast_nonneg _) _) (rpow_nonneg (Nat.cast_nonneg _) _))
    hmem

/-- **Hagedorn gap**: for `σ ≤ 1 + θ` the `F_θ` gas partition sum diverges. -/
theorem not_summable_gas {θ σ : ℝ} (h : σ ≤ 1 + θ) :
    ¬ Summable fun n : ℕ => coeff θ n * (n : ℝ) ^ (-σ) := by
  intro hs
  have hs1 := (summable_nat_add_iff 1).mpr hs
  have hcmp : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (θ - σ) := by
    refine Summable.of_nonneg_of_le (fun n => rpow_nonneg (Nat.cast_nonneg _) _) (fun n => ?_) hs1
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [sub_eq_add_neg, rpow_add hpos]
    exact mul_le_mul_of_nonneg_right (coeff_ge (Nat.succ_ne_zero n)) (rpow_nonneg hpos.le _)
  have hfull : Summable fun n : ℕ => (n : ℝ) ^ (θ - σ) :=
    (summable_nat_add_iff 1).mp (by exact_mod_cast hcmp)
  exact absurd (Real.summable_nat_rpow.mp hfull) (by linarith)

end GppHagedornGapShifted
