/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite section plus tail: a quadratic form that is coercive on a finite block and on its
complement, with small coupling, is nonnegative

A quadratic form on `V ⊕ W` (a finite block `V` with coordinates `c`, a complement `W` with a
vector of size `τ`) splits as `Q = Q_V(c) + 2 Σ c_k b_k + Q_W`. If

* `Q_V(c) ≥ λ Σ d_k c_k²` (the finite block, checked by a matrix certificate; `d_k > 0` are the
  squared norms of an orthogonal basis),
* `Q_W ≥ μ τ²` (the tail is coercive),
* `|b_k| ≤ ε_k τ` (the coupling is small), and
* `Σ ε_k² / d_k ≤ λ μ`,

then `Q ≥ 0`. With `λ, μ` replaced by `λ - δ, μ - δ` the same argument gives `Q ≥ δ (Σ d c² + τ²)`.

This is the bookkeeping step of a computer-assisted lower bound for a quadratic form on a function
space: the finite block is certified by `Matrix.le_quadForm_of_ldl_residual`, the coupling and the
tail by analytic estimates.

## Main results

* `GramTail.two_mul_le_of_sq_le`: the scalar core, `λS + μτ² ≥ 2|X|` from `X² ≤ λS · μτ²`.
* `GramTail.nonneg_of_block_tail`: the statement above.
* `GramTail.ge_of_block_tail`: the version with margin `δ`.
-/

open Finset

namespace GramTail

/-- **Scalar core.** If `X² ≤ (λS)(μτ²)` with `λS, μτ² ≥ 0`, then `-2X ≤ λS + μτ²`. -/
theorem neg_two_mul_le_of_sq_le {X P R : ℝ} (hP : 0 ≤ P) (hR : 0 ≤ R) (h : X ^ 2 ≤ P * R) :
    -(2 * X) ≤ P + R := by
  by_contra hc
  push Not at hc
  have h1 : 0 < -(2 * X) - (P + R) := by linarith
  have h2 : 0 < -(2 * X) + (P + R) := by linarith
  have h3 := mul_pos h1 h2
  nlinarith [sq_nonneg (P - R)]

/-- Cauchy–Schwarz for the coupling: `(Σ c_k b_k)² ≤ τ² (Σ d_k c_k²)(Σ ε_k²/d_k)`. -/
theorem coupling_sq_le {n : ℕ} (c b ε d : Fin n → ℝ) (τ : ℝ) (hd : ∀ k, 0 < d k)
    (hb : ∀ k, |b k| ≤ ε k * τ) :
    (∑ k, c k * b k) ^ 2 ≤ τ ^ 2 * ((∑ k, d k * c k ^ 2) * ∑ k, ε k ^ 2 / d k) := by
  have hτ : ∀ k, 0 ≤ ε k * τ := fun k => (abs_nonneg _).trans (hb k)
  -- |Σ c b| ≤ Σ |c| (ε τ)
  have h1 : |∑ k, c k * b k| ≤ ∑ k, (Real.sqrt (d k) * |c k|) * (ε k * τ / Real.sqrt (d k)) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
    have hs : 0 < Real.sqrt (d k) := Real.sqrt_pos.mpr (hd k)
    rw [abs_mul]
    have : Real.sqrt (d k) * |c k| * (ε k * τ / Real.sqrt (d k)) = |c k| * (ε k * τ) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (hb k) (abs_nonneg (c k))
  have h2 := sum_mul_sq_le_sq_mul_sq univ (fun k => Real.sqrt (d k) * |c k|)
    (fun k => ε k * τ / Real.sqrt (d k))
  have e1 : ∀ k, (Real.sqrt (d k) * |c k|) ^ 2 = d k * c k ^ 2 := by
    intro k; rw [mul_pow, Real.sq_sqrt (hd k).le, sq_abs]
  have e2 : ∀ k, (ε k * τ / Real.sqrt (d k)) ^ 2 = τ ^ 2 * (ε k ^ 2 / d k) := by
    intro k; rw [div_pow, Real.sq_sqrt (hd k).le]; ring
  simp only [e1, e2, ← mul_sum] at h2
  have h0 : 0 ≤ ∑ k, (Real.sqrt (d k) * |c k|) * (ε k * τ / Real.sqrt (d k)) :=
    sum_nonneg fun k _ => mul_nonneg (by positivity) (div_nonneg (hτ k) (Real.sqrt_nonneg _))
  calc (∑ k, c k * b k) ^ 2 = |∑ k, c k * b k| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ k, (Real.sqrt (d k) * |c k|) * (ε k * τ / Real.sqrt (d k))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ ≤ _ := by nlinarith [h2]

/-- **Finite block plus tail.** With `Q_V(c) ≥ λ Σ d c²`, `Q_W ≥ μ τ²`, `|b_k| ≤ ε_k τ` and
`Σ ε_k²/d_k ≤ λ μ` (`λ, μ ≥ 0`), the form `Q_V(c) + 2 Σ c_k b_k + Q_W` is nonnegative. -/
theorem nonneg_of_block_tail {n : ℕ} (QV QW : ℝ) (c b ε d : Fin n → ℝ) (τ lam μ : ℝ)
    (hd : ∀ k, 0 < d k) (hlam : 0 ≤ lam) (hμ : 0 ≤ μ)
    (hV : lam * ∑ k, d k * c k ^ 2 ≤ QV) (hW : μ * τ ^ 2 ≤ QW)
    (hb : ∀ k, |b k| ≤ ε k * τ) (hε : ∑ k, ε k ^ 2 / d k ≤ lam * μ) :
    0 ≤ QV + 2 * ∑ k, c k * b k + QW := by
  set S := ∑ k, d k * c k ^ 2
  have hS : 0 ≤ S := sum_nonneg fun k _ => mul_nonneg (hd k).le (sq_nonneg _)
  have hX := coupling_sq_le c b ε d τ hd hb
  have hX' : (∑ k, c k * b k) ^ 2 ≤ (lam * S) * (μ * τ ^ 2) := by
    calc _ ≤ τ ^ 2 * (S * ∑ k, ε k ^ 2 / d k) := hX
      _ ≤ τ ^ 2 * (S * (lam * μ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hε hS) (sq_nonneg _)
      _ = _ := by ring
  have := neg_two_mul_le_of_sq_le (mul_nonneg hlam hS) (mul_nonneg hμ (sq_nonneg τ)) hX'
  linarith

/-- **With a margin.** If the hypotheses hold with `λ, μ ≥ δ ≥ 0` and
`Σ ε_k²/d_k ≤ (λ - δ)(μ - δ)`, then `Q ≥ δ (Σ d c² + τ²)`. -/
theorem ge_of_block_tail {n : ℕ} (QV QW : ℝ) (c b ε d : Fin n → ℝ) (τ lam μ δ : ℝ)
    (hd : ∀ k, 0 < d k) (hlam : δ ≤ lam) (hμ : δ ≤ μ)
    (hV : lam * ∑ k, d k * c k ^ 2 ≤ QV) (hW : μ * τ ^ 2 ≤ QW)
    (hb : ∀ k, |b k| ≤ ε k * τ) (hε : ∑ k, ε k ^ 2 / d k ≤ (lam - δ) * (μ - δ)) :
    δ * (∑ k, d k * c k ^ 2 + τ ^ 2) ≤ QV + 2 * ∑ k, c k * b k + QW := by
  have h := nonneg_of_block_tail (QV - δ * ∑ k, d k * c k ^ 2) (QW - δ * τ ^ 2) c b ε d τ
    (lam - δ) (μ - δ) hd (by linarith) (by linarith) (by nlinarith) (by nlinarith) hb hε
  linarith

end GramTail

#print axioms GramTail.nonneg_of_block_tail
#print axioms GramTail.ge_of_block_tail
