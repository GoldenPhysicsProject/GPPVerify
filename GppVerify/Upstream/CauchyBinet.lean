/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# The Cauchy–Binet formula

For `A : Matrix (Fin n) (Fin m) R` and `B : Matrix (Fin m) (Fin n) R` over a commutative ring,

`det (A * B) = ∑ S ⊆ Fin m, |S| = n, det (A_{·,S}) * det (B_{S,·})`,

where `A_{·,S}` keeps the columns of `A` in `S` (in increasing order) and `B_{S,·}` keeps the rows
of `B` in `S`. (For `m < n` the sum is empty and `det (A * B) = 0`.)

The proof expands `det (A * B)` over all functions `f : Fin n → Fin m`, discards the non-injective
ones (equal columns), and parametrises the injective ones by the pair (image `S`, permutation `τ`)
via `f = (S.orderEmbOfFin) ∘ τ`.

No `sorry`, no `axiom`.
-/

namespace Matrix

open Finset Equiv

variable {R : Type*} [CommRing R] {n m : ℕ}

/-- Expansion over all functions `f : Fin n → Fin m`. -/
theorem det_mul_eq_sum_fun (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) :
    (A * B).det = ∑ f : Fin n → Fin m, (∏ i, B (f i) i) * (A.submatrix id f).det := by
  rw [det_apply']
  simp_rw [mul_apply]
  have h1 : ∀ σ : Perm (Fin n), (∏ i, ∑ k, A (σ i) k * B k i)
      = ∑ f : Fin n → Fin m, ∏ i, (A (σ i) (f i) * B (f i) i) := by
    intro σ
    have := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin m)))
      (fun i k => A (σ i) k * B k i)
    rw [this]
    rfl
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id_eq, Finset.prod_mul_distrib]
  ring


/-- The column selection of an `n`-element subset `S ⊆ Fin m`, in increasing order. -/
noncomputable def colSel (S : {S : Finset (Fin m) // S.card = n}) : Fin n → Fin m :=
  S.1.orderEmbOfFin S.2

theorem colSel_injective (S : {S : Finset (Fin m) // S.card = n}) :
    Function.Injective (colSel S) :=
  (S.1.orderEmbOfFin S.2).injective

theorem range_colSel (S : {S : Finset (Fin m) // S.card = n}) :
    Set.range (colSel S) = (S.1 : Set (Fin m)) :=
  Finset.range_orderEmbOfFin S.1 S.2

/-- The parametrisation `(S, τ) ↦ colSel S ∘ τ` of injective functions. -/
noncomputable def param (p : {S : Finset (Fin m) // S.card = n} × Perm (Fin n)) : Fin n → Fin m :=
  colSel p.1 ∘ p.2

theorem param_injective : Function.Injective (param (n := n) (m := m)) := by
  rintro ⟨S, τ⟩ ⟨S', τ'⟩ h
  have hS : S = S' := by
    apply Subtype.ext
    apply Finset.coe_injective
    rw [← range_colSel S, ← range_colSel S']
    have h1 : Set.range (colSel S) = Set.range (colSel S ∘ τ) :=
      (Function.Surjective.range_comp τ.surjective _).symm
    have h2 : Set.range (colSel S') = Set.range (colSel S' ∘ τ') :=
      (Function.Surjective.range_comp τ'.surjective _).symm
    rw [h1, h2]
    exact congrArg Set.range h
  subst hS
  have hτ : τ = τ' := Equiv.ext fun i => colSel_injective S (congrFun h i)
  rw [hτ]

theorem mem_range_param_iff (f : Fin n → Fin m) :
    f ∈ Set.range (param (n := n) (m := m)) ↔ Function.Injective f := by
  constructor
  · rintro ⟨⟨S, τ⟩, rfl⟩
    exact (colSel_injective S).comp τ.injective
  · intro hf
    have hcard : (Finset.univ.image f).card = n := by
      rw [Finset.card_image_of_injective _ hf]; simp
    set S : {S : Finset (Fin m) // S.card = n} := ⟨Finset.univ.image f, hcard⟩ with hSdef
    have hmem : ∀ i, f i ∈ Set.range (colSel S) := by
      intro i
      rw [range_colSel]
      simp [hSdef]
    choose τ₀ hτ₀ using hmem
    have hinj : Function.Injective τ₀ := by
      intro i j hij
      apply hf
      rw [← hτ₀ i, ← hτ₀ j, hij]
    have hbij : Function.Bijective τ₀ := Finite.injective_iff_bijective.mp hinj
    refine ⟨(S, Equiv.ofBijective τ₀ hbij), ?_⟩
    funext i
    simp [param, hτ₀]


/-- **Cauchy–Binet formula.** -/
theorem det_mul_eq_sum_subsets (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) :
    (A * B).det = ∑ S : {S : Finset (Fin m) // S.card = n},
      (A.submatrix id (colSel S)).det * (B.submatrix (colSel S) id).det := by
  rw [det_mul_eq_sum_fun]
  set T : (Fin n → Fin m) → R := fun f => (∏ i, B (f i) i) * (A.submatrix id f).det with hT
  have h0 : ∀ f : Fin n → Fin m, ¬ Function.Injective f → T f = 0 := by
    intro f hf
    rw [Function.Injective] at hf
    push Not at hf
    obtain ⟨i, j, hij, hne⟩ := hf
    have : (A.submatrix id f).det = 0 :=
      det_zero_of_column_eq hne (fun k => by simp [hij])
    simp [hT, this]
  have h1 : ∑ f : Fin n → Fin m, T f
      = ∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin m => Function.Injective f), T f := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f _ hf
    exact h0 f (by simpa using hf)
  have h2 : Finset.univ.filter (fun f : Fin n → Fin m => Function.Injective f)
      = Finset.univ.image (param (n := n) (m := m)) := by
    ext f
    simp [← mem_range_param_iff, Set.mem_range]
  rw [h1, h2, Finset.sum_image (fun p _ q _ h => param_injective h), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun S _ => ?_
  -- inner sum over permutations
  have hperm : ∀ τ : Perm (Fin n), T (param (S, τ))
      = (A.submatrix id (colSel S)).det *
        (Perm.sign τ * ∏ i, B (colSel S (τ i)) i) := by
    intro τ
    have e : (A.submatrix id (param (S, τ))) = (A.submatrix id (colSel S)).submatrix id τ := by
      ext i j; simp [param]
    simp only [hT, e, det_permute']
    simp only [param, Function.comp_apply]
    ring
  simp_rw [hperm]
  rw [← Finset.mul_sum, det_apply' (B.submatrix (colSel S) id)]
  simp only [submatrix_apply, id_eq]

end Matrix

#print axioms Matrix.det_mul_eq_sum_subsets
