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

end Matrix
