/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statements from Heart of the Cosmos / Grok)
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Vandermonde
import GppVerify.Upstream.CauchyBinet

/-!
# Hankel determinants of a finite measure via Cauchy–Binet (Heart claim #18, `HR20_hankel_cauchy_binet`)

Let `x_1, …, x_m` and `w_1, …, w_m` be elements of a commutative ring and `c_j = Σ_i w_i x_i^j`.
For `n ≤ m`:

* `hankel_det_eq_sum`:   `det (c_{r+s})_{r,s<n}   = Σ_{S ⊆ [m], |S| = n} (Π_{i∈S} w_i) · V(S)²`;
* `hankel_shift_det_eq_sum`: `det (c_{r+s+1})_{r,s<n} = Σ_S (Π_{i∈S} w_i x_i) · V(S)²`,

with `V(S)` the Vandermonde determinant of the nodes in `S` (`Matrix.vandermonde`). Over `ℝ` with
positive weights and distinct positive nodes, both determinants are strictly positive for `n ≤ m`
(`hankel_det_pos`, `hankel_shift_det_pos`).

The factorisation `(c_{r+s}) = A B` with `A_{r,i} = w_i x_i^r`, `B_{i,s} = x_i^s` and the general
Cauchy–Binet formula (`Matrix.det_mul_eq_sum_subsets`) do the work. No `sorry`, no `axiom`.
-/

namespace GppHankel

open Finset Matrix

variable {R : Type*} [CommRing R] {n m : ℕ}

/-- The Hankel matrix `(Σ_i w_i x_i^{r+s})_{r,s<n}`. -/
def hankel (x w : Fin m → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun r s => ∑ i, w i * x i ^ ((r : ℕ) + (s : ℕ))

theorem prod_colSel (w : Fin m → R) (S : {S : Finset (Fin m) // S.card = n}) :
    ∏ j : Fin n, w (Matrix.colSel S j) = ∏ i ∈ S.1, w i := by
  have hmap : (Finset.univ.map ⟨Matrix.colSel S, Matrix.colSel_injective S⟩ : Finset (Fin m))
      = S.1 := by
    apply Finset.coe_injective
    simp [Matrix.range_colSel]
  rw [← hmap, Finset.prod_map]
  rfl

/-- **Heart claim #18, first formula.** -/
theorem hankel_det_eq_sum (x w : Fin m → R) :
    (hankel x w n).det = ∑ S : {S : Finset (Fin m) // S.card = n},
      (∏ i ∈ S.1, w i) * (Matrix.vandermonde (x ∘ Matrix.colSel S)).det ^ 2 := by
  have hfac : hankel x w n
      = (Matrix.of fun (r : Fin n) (i : Fin m) => x i ^ (r : ℕ) * w i)
        * (Matrix.of fun (i : Fin m) (s : Fin n) => x i ^ (s : ℕ)) := by
    ext r s
    simp only [hankel, Matrix.of_apply, Matrix.mul_apply, pow_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hfac, Matrix.det_mul_eq_sum_subsets]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hB : (Matrix.of (fun (i : Fin m) (s : Fin n) => x i ^ (s : ℕ))).submatrix
      (Matrix.colSel S) id = Matrix.vandermonde (x ∘ Matrix.colSel S) := by
    ext j s; simp [Matrix.vandermonde]
  have hA : (Matrix.of (fun (r : Fin n) (i : Fin m) => x i ^ (r : ℕ) * w i)).submatrix id
      (Matrix.colSel S) = (Matrix.vandermonde (x ∘ Matrix.colSel S)).transpose
        * Matrix.diagonal (fun j => w (Matrix.colSel S j)) := by
    ext r j
    simp [Matrix.vandermonde, Matrix.mul_apply, Matrix.diagonal_apply]
  rw [hB, hA, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, prod_colSel]
  ring

/-- **Heart claim #18, shifted formula.** -/
theorem hankel_shift_det_eq_sum (x w : Fin m → R) :
    (hankel x (fun i => w i * x i) n).det = ∑ S : {S : Finset (Fin m) // S.card = n},
      (∏ i ∈ S.1, (w i * x i)) * (Matrix.vandermonde (x ∘ Matrix.colSel S)).det ^ 2 :=
  hankel_det_eq_sum x (fun i => w i * x i)

/-- The shifted Hankel matrix is the Hankel matrix of the shifted weights `w_i x_i`:
`Σ_i w_i x_i^{r+s+1}`. -/
theorem hankel_shift_entry (x w : Fin m → R) (r s : Fin n) :
    hankel x (fun i => w i * x i) n r s = ∑ i, w i * x i ^ ((r : ℕ) + (s : ℕ) + 1) := by
  simp only [hankel, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring


/-- **Corollary.** Positive weights and distinct nodes give a positive Hankel determinant for
`n ≤ m`. -/
theorem hankel_det_pos {x w : Fin m → ℝ} (hw : ∀ i, 0 < w i) (hx : Function.Injective x)
    (hn : n ≤ m) : 0 < (hankel x w n).det := by
  rw [hankel_det_eq_sum]
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq
    (show n ≤ (Finset.univ : Finset (Fin m)).card by simpa using hn)
  apply Finset.sum_pos
  · intro S _
    have hV : (Matrix.vandermonde (x ∘ Matrix.colSel S)).det ≠ 0 :=
      Matrix.det_vandermonde_ne_zero_iff.mpr (hx.comp (Matrix.colSel_injective S))
    exact mul_pos (Finset.prod_pos fun i _ => hw i) (by positivity)
  · exact ⟨⟨T, hT⟩, Finset.mem_univ _⟩

/-- **Corollary.** Positive weights and distinct positive nodes give a positive shifted Hankel
determinant `det (Σ_i w_i x_i^{r+s+1})` for `n ≤ m`. -/
theorem hankel_shift_det_pos {x w : Fin m → ℝ} (hw : ∀ i, 0 < w i) (hxpos : ∀ i, 0 < x i)
    (hx : Function.Injective x) (hn : n ≤ m) :
    0 < (hankel x (fun i => w i * x i) n).det :=
  hankel_det_pos (fun i => mul_pos (hw i) (hxpos i)) hx hn

end GppHankel

#print axioms GppHankel.hankel_det_eq_sum
#print axioms GppHankel.hankel_shift_det_eq_sum
#print axioms GppHankel.hankel_det_pos
#print axioms GppHankel.hankel_shift_det_pos
