import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# No diagonal Hilbert reweighting of the prime space can repair the primitive current

Source: Codex, GPPDiscovery2 `research/2026-09-27_vector_prime_current_scalarization_nogo.md`, §3.

Let `w_p > 0` be positive weights on the primes and `‖c‖_w² = Σ_p w_p |c_p|²`.

* (A) the primitive coefficient vector `a_p = (log p)/√p` lies in `H_w` iff
  `Σ_p w_p (log p)² / p < ∞`;
* (B) the all-ones scalarization `ℓ_∞(c) = Σ_p c_p` is bounded on `H_w` iff `Σ_p 1/w_p < ∞`.

`no_diagonal_fix`: (A) and (B) cannot both hold. By AM–GM, `w_p(log p)²/p + 1/w_p ≥ 2 (log p)/√p
≥ 1/p`, so (A) and (B) would make `Σ_p 1/p` converge, contradicting Euler's divergence of the prime
harmonic series (Mathlib: `Nat.Primes.not_summable_one_div`).

## Checks and scope

The claim checks; the proof avoids square roots by comparing squares. **Not formalized:** the
temperedness of the vector-valued current `J_vec ∈ S'(ℝ; ℓ²(P))` (§1), the identification of (A)/(B)
with membership/boundedness (stated above as the definitions of the two conditions), and the
Abel-regulated half-density wall (§5). The note's consequence — any completion must be non-diagonal —
is the reading of this theorem, not part of it. No RH claim.
-/

open Real

namespace GppPrimeWeightNoGo

/-- **No positive diagonal reweighting satisfies both (A) and (B).** -/
theorem no_diagonal_fix (w : Nat.Primes → ℝ) (hw : ∀ p, 0 < w p) :
    ¬ (Summable (fun p : Nat.Primes => w p * Real.log p ^ 2 / (p : ℝ)) ∧
        Summable (fun p : Nat.Primes => 1 / w p)) := by
  rintro ⟨hA, hB⟩
  apply Nat.Primes.not_summable_one_div
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (hA.add hB)
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hl : (1 / 2 : ℝ) ≤ Real.log p := by
    have h2 := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp
    linarith
  have hw0 := hw p
  set a : ℝ := w p * Real.log p ^ 2 / p with ha
  set b : ℝ := 1 / w p with hb
  have hab : a * b = Real.log p ^ 2 / p := by
    rw [ha, hb]; field_simp
  have hapos : 0 < a := by rw [ha]; positivity
  have hbpos : 0 < b := by rw [hb]; positivity
  -- (a + b)^2 ≥ 4ab = 4 (log p)^2 / p ≥ 1/p^2
  have h4 : (1 / (p : ℝ)) ^ 2 ≤ (a + b) ^ 2 := by
    have h1 : 4 * (a * b) ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
    have h2 : (1 / (p : ℝ)) ^ 2 ≤ 4 * (a * b) := by
      rw [hab, div_pow, one_pow, show (4 : ℝ) * (Real.log p ^ 2 / p) = 4 * Real.log p ^ 2 / p by ring,
        div_le_div_iff₀ (by positivity) hp0]
      have hl2 : (1 / 4 : ℝ) ≤ Real.log p ^ 2 := by nlinarith
      have h3 : 1 ≤ 4 * Real.log p ^ 2 * p := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h3 hp0.le]
    linarith
  by_contra hlt
  have hlt' : a + b < 1 / (p : ℝ) := not_le.mp hlt
  have : (a + b) ^ 2 < (1 / (p : ℝ)) ^ 2 :=
    pow_lt_pow_left₀ hlt' (by positivity) (by norm_num)
  linarith

end GppPrimeWeightNoGo
