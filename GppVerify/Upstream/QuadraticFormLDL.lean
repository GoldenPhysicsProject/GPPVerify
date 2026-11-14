/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Chebyshev

/-!
# Lower bounds for quadratic forms from an `L D Lᵀ` certificate

A finite real quadratic form `x ↦ Σ_{i,j} M i j x_i x_j` is bounded below by `δ Σ x_i²` as soon as
`M = δ I + L D Lᵀ` entrywise, for some matrix `L` and some nonnegative diagonal `D`. The identity is
a finite set of exact equalities, so a computer can supply `L` and `D` (for example from a shifted
Cholesky or `LDLᵀ` factorisation over `ℚ`) and the equalities can be checked by evaluation. This
file proves the implication once. It is the positive-definiteness step of a computer-assisted
lower bound.

## Main results

* `Matrix.quadForm_ldl`: if `M i j = δ [i = j] + Σ_k L i k D k L j k`, then
  `Σ_{i,j} M i j x_i x_j = δ Σ_i x_i² + Σ_k D k (Σ_i L i k x_i)²`.
* `Matrix.le_quadForm_of_ldl`: with `D ≥ 0`, `δ Σ_i x_i² ≤ Σ_{i,j} M i j x_i x_j`.
* `Matrix.le_quadForm_of_ldl_residual`: the same with a rounded factorisation. If every entry of
  `M - (δ I + L D Lᵀ)` is at most `ε` in absolute value, then `(δ - n ε) Σ x_i² ≤ Σ M i j x_i x_j`.
  So a certificate may carry short (rounded) rationals for `L` and `D`, and the exact check is only
  the entrywise residual bound.
-/

open Finset

namespace Matrix

variable {n : ℕ}

/-- **The `L D Lᵀ` identity for the quadratic form.** -/
theorem quadForm_ldl (M L : Fin n → Fin n → ℝ) (D : Fin n → ℝ) (δ : ℝ)
    (hM : ∀ i j, M i j = (if i = j then δ else 0) + ∑ k, L i k * D k * L j k) (x : Fin n → ℝ) :
    ∑ i, ∑ j, M i j * x i * x j = δ * ∑ i, x i ^ 2 + ∑ k, D k * (∑ i, L i k * x i) ^ 2 := by
  simp_rw [hM, add_mul, sum_add_distrib]
  congr 1
  · simp only [ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true, mul_sum]
    refine sum_congr rfl fun i _ => by ring
  · have h1 : ∀ i j, (∑ k, L i k * D k * L j k) * x i * x j =
        ∑ k, D k * ((L i k * x i) * (L j k * x j)) := by
      intro i j
      rw [sum_mul, sum_mul]
      exact sum_congr rfl fun k _ => by ring
    have h2 : ∀ k, D k * (∑ i, L i k * x i) ^ 2 =
        ∑ i, ∑ j, D k * ((L i k * x i) * (L j k * x j)) := by
      intro k
      rw [sq, sum_mul_sum, mul_sum]
      exact sum_congr rfl fun i _ => by rw [mul_sum]
    simp_rw [h1, h2]
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]

/-- **Lower bound from an `L D Lᵀ` certificate.** If `M = δ I + L D Lᵀ` entrywise with `D ≥ 0`,
then `δ Σ x_i² ≤ Σ_{i,j} M i j x_i x_j` for every `x`. -/
theorem le_quadForm_of_ldl (M L : Fin n → Fin n → ℝ) (D : Fin n → ℝ) (δ : ℝ)
    (hM : ∀ i j, M i j = (if i = j then δ else 0) + ∑ k, L i k * D k * L j k)
    (hD : ∀ k, 0 ≤ D k) (x : Fin n → ℝ) :
    δ * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, M i j * x i * x j := by
  rw [quadForm_ldl M L D δ hM x]
  have : 0 ≤ ∑ k, D k * (∑ i, L i k * x i) ^ 2 :=
    sum_nonneg fun k _ => mul_nonneg (hD k) (sq_nonneg _)
  linarith

/-- A rational certificate transfers to the reals: if the identity holds over `ℚ`, the real form
inherits the bound. -/
theorem le_quadForm_of_ldl_rat (M L : Fin n → Fin n → ℚ) (D : Fin n → ℚ) (δ : ℚ)
    (hM : ∀ i j, M i j = (if i = j then δ else 0) + ∑ k, L i k * D k * L j k)
    (hD : ∀ k, 0 ≤ D k) (x : Fin n → ℝ) :
    (δ : ℝ) * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, (M i j : ℝ) * x i * x j := by
  refine le_quadForm_of_ldl (fun i j => (M i j : ℝ)) (fun i j => (L i j : ℝ)) (fun k => (D k : ℝ))
    δ (fun i j => ?_) (fun k => Rat.cast_nonneg.mpr (hD k)) x
  rw [hM i j]
  split_ifs <;> push_cast <;> ring

/-- An entrywise bound `|E i j| ≤ ε` controls the quadratic form: `-(n ε) Σ x_i² ≤ Σ E i j x_i x_j`. -/
theorem neg_card_mul_le_quadForm (E : Fin n → Fin n → ℝ) (ε : ℝ) (hE : ∀ i j, |E i j| ≤ ε)
    (x : Fin n → ℝ) : -(n * ε) * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, E i j * x i * x j := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hE ⟨0, hn⟩ ⟨0, hn⟩)
  have h1 : ∀ i j, -(ε * (|x i| * |x j|)) ≤ E i j * x i * x j := by
    intro i j
    have : |E i j * x i * x j| ≤ ε * (|x i| * |x j|) := by
      rw [abs_mul, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_right (hE i j) (by positivity)
    exact (abs_le.mp this).1
  have h2 : -(ε * (∑ i, |x i|) ^ 2) ≤ ∑ i, ∑ j, E i j * x i * x j := by
    have : ∑ i, ∑ j, -(ε * (|x i| * |x j|)) = -(ε * (∑ i, |x i|) ^ 2) := by
      rw [sq, sum_mul_sum]
      simp only [sum_neg_distrib, mul_sum]
    rw [← this]
    exact sum_le_sum fun i _ => sum_le_sum fun j _ => h1 i j
  have h3 : (∑ i, |x i|) ^ 2 ≤ n * ∑ i, x i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := fun i => |x i|)
    simpa [sq_abs] using this
  nlinarith [mul_le_mul_of_nonneg_left h3 hε]

/-- **Lower bound from a rounded `L D Lᵀ` certificate.** If every entry of `M - (δ I + L D Lᵀ)` is
bounded by `ε` and `D ≥ 0`, then `(δ - n ε) Σ x_i² ≤ Σ_{i,j} M i j x_i x_j`. -/
theorem le_quadForm_of_ldl_residual (M L : Fin n → Fin n → ℝ) (D : Fin n → ℝ) (δ ε : ℝ)
    (hM : ∀ i j, |M i j - ((if i = j then δ else 0) + ∑ k, L i k * D k * L j k)| ≤ ε)
    (hD : ∀ k, 0 ≤ D k) (x : Fin n → ℝ) :
    (δ - n * ε) * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, M i j * x i * x j := by
  set A : Fin n → Fin n → ℝ := fun i j => (if i = j then δ else 0) + ∑ k, L i k * D k * L j k
  have hA := le_quadForm_of_ldl A L D δ (fun i j => rfl) hD x
  have hE := neg_card_mul_le_quadForm (fun i j => M i j - A i j) ε hM x
  have hsplit : ∑ i, ∑ j, M i j * x i * x j =
      ∑ i, ∑ j, A i j * x i * x j + ∑ i, ∑ j, (M i j - A i j) * x i * x j := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  rw [hsplit]
  nlinarith

/-- The rounded certificate over `ℚ`: the residual bound is a finite rational check. -/
theorem le_quadForm_of_ldl_residual_rat (M L : Fin n → Fin n → ℚ) (D : Fin n → ℚ) (δ ε : ℚ)
    (hM : ∀ i j, |M i j - ((if i = j then δ else 0) + ∑ k, L i k * D k * L j k)| ≤ ε)
    (hD : ∀ k, 0 ≤ D k) (x : Fin n → ℝ) :
    ((δ : ℝ) - n * ε) * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, (M i j : ℝ) * x i * x j := by
  refine le_quadForm_of_ldl_residual (fun i j => (M i j : ℝ)) (fun i j => (L i j : ℝ))
    (fun k => (D k : ℝ)) δ ε (fun i j => ?_) (fun k => Rat.cast_nonneg.mpr (hD k)) x
  have h := hM i j
  split_ifs at h ⊢ <;> exact_mod_cast h

end Matrix
