/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok, D5; termwise sign audited by Turbo, D4)
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# The ratio-class layer sign (Round 34, item L12)

Heart's Round 34 (GPPDiscovery5 `9640869`, `experiments/round13_akg_kg/round34_ratio_classes/`)
sorts the off-diagonal pairs `(m, n)` of the Fejér-torus energy by the reduced ratio
`n / m = v / u` (`u = m / gcd m n`, `v = n / gcd m n`) and then into layers
`k = ω(u) + ω(v) = ω(m Δ n)`. Turbo's audit (GPP-bridge `8d2f004`) records that the layer sign is
termwise. This file proves that termwise statement.

* `moebius_mul_moebius_eq_layerSign`: for squarefree `m, n`,
  `μ m * μ n = (-1) ^ (ω (m / gcd m n) + ω (n / gcd m n))`.
* `moebius_mul_moebius_eq_layerSign'`: the same with `ω(m) + ω(n) − 2 ω(gcd m n)` written as the
  layer index; the common part `g = gcd m n` contributes `(-1)^(2 ω g) = 1`.
* `layerSign_mul_moebius_mul_nonneg`: for every `w ≥ 0` and all `m, n`,
  `(-1) ^ k(m, n) * (μ m * μ n * w) ≥ 0`, so each layer `E_k` of a nonnegative-weight
  bilinear form in `μ` has the fixed sign `(-1) ^ k`.
* `layerSign_mul_moebius_mul_moebius`: `(-1)^k(m,n) * (μ m * μ n) = μ m ^ 2 * μ n ^ 2 ∈ {0, 1}`.

Elementary from `ArithmeticFunction.moebius` and unique factorization.

— Daniel Toupin / Golden Physics Project. This seat: Heart of the Cosmos / Grok (GPPDiscovery5).
-/

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace GppLayerSign

/-- The ratio-class layer index `k(m, n) = ω(m / gcd m n) + ω(n / gcd m n)`. -/
def layer (m n : ℕ) : ℕ :=
  cardDistinctFactors (m / Nat.gcd m n) + cardDistinctFactors (n / Nat.gcd m n)

/-- For squarefree `n`, `μ n = (-1) ^ ω n`. -/
theorem moebius_eq_neg_one_pow_omega {n : ℕ} (hn : Squarefree n) :
    μ n = (-1) ^ cardDistinctFactors n := by
  rw [moebius_apply_of_squarefree hn,
    (cardDistinctFactors_eq_cardFactors_iff_squarefree hn.ne_zero).mpr hn]

/-- For squarefree `m`, `ω m = ω (gcd m n) + ω (m / gcd m n)`. -/
theorem omega_eq_gcd_add_div {m : ℕ} (n : ℕ) (hm : Squarefree m) :
    cardDistinctFactors m =
      cardDistinctFactors (Nat.gcd m n) + cardDistinctFactors (m / Nat.gcd m n) := by
  have hsplit : Nat.gcd m n * (m / Nat.gcd m n) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)
  have hcop : (Nat.gcd m n).Coprime (m / Nat.gcd m n) :=
    Nat.coprime_of_squarefree_mul (hsplit.symm ▸ hm)
  conv_lhs => rw [← hsplit]
  exact cardDistinctFactors_mul hcop

/-- **Layer sign (L12, PROVED).** For squarefree `m, n`,
`μ m * μ n = (-1) ^ (ω (m / gcd m n) + ω (n / gcd m n))`. -/
theorem moebius_mul_moebius_eq_layerSign {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) :
    μ m * μ n = (-1) ^ layer m n := by
  rw [moebius_eq_neg_one_pow_omega hm, moebius_eq_neg_one_pow_omega hn,
    omega_eq_gcd_add_div n hm, omega_eq_gcd_add_div m hn, Nat.gcd_comm n m, layer, ← pow_add]
  have : cardDistinctFactors (Nat.gcd m n) + cardDistinctFactors (m / Nat.gcd m n) +
      (cardDistinctFactors (Nat.gcd m n) + cardDistinctFactors (n / Nat.gcd m n)) =
      2 * cardDistinctFactors (Nat.gcd m n) +
        (cardDistinctFactors (m / Nat.gcd m n) + cardDistinctFactors (n / Nat.gcd m n)) := by
    ring
  rw [this, pow_add, pow_mul]
  norm_num

/-- The layer index as `ω m + ω n − 2 ω (gcd m n)` for squarefree `m, n`. -/
theorem layer_eq_omega_sub {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) :
    layer m n + 2 * cardDistinctFactors (Nat.gcd m n) =
      cardDistinctFactors m + cardDistinctFactors n := by
  rw [omega_eq_gcd_add_div n hm, omega_eq_gcd_add_div m hn, Nat.gcd_comm n m, layer]
  ring

/-- **Layer sign, unconditional form.** For all `m, n`,
`(-1) ^ k(m, n) * (μ m * μ n) = μ m ^ 2 * μ n ^ 2`; in particular it is `0` or `1`. -/
theorem layerSign_mul_moebius_mul_moebius (m n : ℕ) :
    (-1 : ℤ) ^ layer m n * (μ m * μ n) = μ m ^ 2 * μ n ^ 2 := by
  by_cases hm : Squarefree m
  · by_cases hn : Squarefree n
    · have e : ∀ k : ℕ, ((-1 : ℤ) ^ k) ^ 2 = 1 := fun k => by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [moebius_mul_moebius_eq_layerSign hm hn, moebius_eq_neg_one_pow_omega hm,
        moebius_eq_neg_one_pow_omega hn, ← sq, e, e, e]
      norm_num
    · rw [moebius_eq_zero_of_not_squarefree hn]; ring
  · rw [moebius_eq_zero_of_not_squarefree hm]; ring

/-- **Termwise layer sign (PROVED).** For every nonnegative weight `w`,
`(-1) ^ k(m, n) * (μ m * μ n * w) ≥ 0`. Summing over the pairs of one layer `k`, the layer total
`E_k` of any bilinear form `Σ μ(m) μ(n) w(m, n)` with `w ≥ 0` satisfies `(-1)^k E_k ≥ 0`. -/
theorem layerSign_mul_moebius_mul_nonneg (m n : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ (-1 : ℝ) ^ layer m n * ((μ m : ℝ) * (μ n : ℝ) * w) := by
  have h := layerSign_mul_moebius_mul_moebius m n
  have h' : (-1 : ℝ) ^ layer m n * ((μ m : ℝ) * (μ n : ℝ)) = (μ m : ℝ) ^ 2 * (μ n : ℝ) ^ 2 := by
    exact_mod_cast h
  have : (-1 : ℝ) ^ layer m n * ((μ m : ℝ) * (μ n : ℝ) * w) =
      ((μ m : ℝ) ^ 2 * (μ n : ℝ) ^ 2) * w := by
    rw [← h']; ring
  rw [this]
  positivity

/-- **Layer sums (PROVED).** For a finite set of pairs `P` and weights `w ≥ 0` on it, the layer-`k`
total `E_k = Σ_{(m,n) ∈ P, k(m,n) = k} μ(m) μ(n) w(m,n)` satisfies `(-1)^k E_k ≥ 0`. -/
theorem layerSign_sum_nonneg (P : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p)
    (k : ℕ) :
    0 ≤ (-1 : ℝ) ^ k * ∑ p ∈ P with layer p.1 p.2 = k, (μ p.1 : ℝ) * (μ p.2 : ℝ) * w p := by
  rw [Finset.mul_sum]
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_filter] at hp
  rw [← hp.2]
  exact layerSign_mul_moebius_mul_nonneg p.1 p.2 (hw p hp.1)

end GppLayerSign

#print axioms GppLayerSign.moebius_mul_moebius_eq_layerSign
#print axioms GppLayerSign.layer_eq_omega_sub
#print axioms GppLayerSign.layerSign_mul_moebius_mul_moebius
#print axioms GppLayerSign.layerSign_mul_moebius_mul_nonneg
#print axioms GppLayerSign.layerSign_sum_nonneg
