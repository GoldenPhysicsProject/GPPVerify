import Mathlib.Tactic

/-!
# *Which Way Is Forward?*: family-product signs (G4, layer A)

Abstract layer for the parent charge-conjugation signs of
`verify_wwif.py` (function `verify_parent_charge_conjugation_signs`).

For a list of pairwise anticommuting matrices with known squares
`A * A = sq A • 1` and known entrywise-conjugation eigenvalues
`A.map (starRingEnd ℂ) = δ A • A`, the family product `B = L.prod`
satisfies

`B * B.map (starRingEnd ℂ) = ((L.map δ).prod * (-1) ^ (pairs L) * (L.map sq).prod) • 1`,

where `pairs L` counts the factor pairs, `L.length * (L.length - 1) / 2`
in recursive form. This is the `B Bbar` sign mechanism: no large matrices
are involved, only the anticommutation crossing count, the product of
squares, and the product of conjugation eigenvalues.

Scope: this layer proves the sign formula for an abstract family. The
concrete Pauli-string families for `Spin(6,2)` and `Spin(10,2)` that
instantiate it, and the uniform intertwining sign, are the concrete
layer built on top of this one.
-/

namespace GppWhichWayForwardFamilySigns

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pair count of a list, recursively: `pairs (A :: L) = L.length + pairs L`.
For a list of length `m` this is `m * (m - 1) / 2`, computed by recursion so
that concrete evaluations are definitional. -/
def pairs : List (Matrix n n ℂ) → ℕ
  | [] => 0
  | _ :: L => L.length + pairs L

/-- Moving a matrix past a product of factors it anticommutes with
costs one sign per factor. -/
theorem prod_mul_of_anticommutes {A : Matrix n n ℂ} :
    ∀ L : List (Matrix n n ℂ), (∀ B ∈ L, A * B = -(B * A)) →
      L.prod * A = (-1 : ℂ) ^ L.length • (A * L.prod)
  | [], _ => by simp
  | B :: L, h => by
    have hL : ∀ C ∈ L, A * C = -(C * A) := fun C hC => h C (List.mem_cons_of_mem B hC)
    have hB : A * B = -(B * A) := h B List.mem_cons_self
    have hB' : B * A = -(A * B) := by rw [hB, neg_neg]
    calc (B :: L).prod * A = B * (L.prod * A) := by
            rw [List.prod_cons, mul_assoc]
      _ = B * ((-1 : ℂ) ^ L.length • (A * L.prod)) := by
            rw [prod_mul_of_anticommutes L hL]
      _ = (-1 : ℂ) ^ L.length • (B * (A * L.prod)) := by
            rw [Matrix.mul_smul]
      _ = (-1 : ℂ) ^ L.length • ((B * A) * L.prod) := by rw [mul_assoc]
      _ = (-1 : ℂ) ^ L.length • (-(A * (B * L.prod))) := by
            rw [hB', neg_mul, mul_assoc]
      _ = (-1 : ℂ) ^ (B :: L).length • (A * (B :: L).prod) := by
            rw [List.prod_cons, List.length_cons, pow_succ, ← smul_smul,
              neg_one_smul]

/-- The square of a product of pairwise anticommuting matrices is the
crossing sign times the product of the squares. -/
theorem prod_sq_of_pairwise {sq : Matrix n n ℂ → ℂ} :
    ∀ L : List (Matrix n n ℂ), L.Nodup →
      (∀ A ∈ L, ∀ B ∈ L, A ≠ B → A * B = -(B * A)) →
      (∀ A ∈ L, A * A = sq A • 1) →
      L.prod * L.prod = ((-1 : ℂ) ^ pairs L * (L.map sq).prod) • 1
  | [], _, _, _ => by simp [pairs]
  | A :: L, hnd, hanti, hsq => by
    have hnd' : L.Nodup := (List.nodup_cons.mp hnd).2
    have hA : A ∉ L := (List.nodup_cons.mp hnd).1
    have hantiL : ∀ B ∈ L, ∀ C ∈ L, B ≠ C → B * C = -(C * B) :=
      fun B hB C hC hne => hanti B (List.mem_cons_of_mem A hB) C (List.mem_cons_of_mem A hC) hne
    have hsqL : ∀ B ∈ L, B * B = sq B • 1 :=
      fun B hB => hsq B (List.mem_cons_of_mem A hB)
    have hsqA : A * A = sq A • 1 := hsq A List.mem_cons_self
    have hmove : ∀ B ∈ L, A * B = -(B * A) :=
      fun B hB => hanti A List.mem_cons_self B (List.mem_cons_of_mem A hB)
        (fun he => hA (he ▸ hB))
    have ih := prod_sq_of_pairwise L hnd' hantiL hsqL
    have hstep := prod_mul_of_anticommutes L hmove
    calc (A :: L).prod * (A :: L).prod
        = A * (L.prod * A) * L.prod := by
          rw [List.prod_cons]
          simp only [mul_assoc]
      _ = A * ((-1 : ℂ) ^ L.length • (A * L.prod)) * L.prod := by rw [hstep]
      _ = ((-1 : ℂ) ^ L.length * sq A) • (L.prod * L.prod) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, ← mul_assoc A A L.prod, hsqA,
            Matrix.smul_mul, one_mul, Matrix.smul_mul, smul_smul]
      _ = ((-1 : ℂ) ^ L.length * sq A) •
            (((-1 : ℂ) ^ pairs L * (L.map sq).prod) • 1) := by rw [ih]
      _ = ((-1 : ℂ) ^ pairs (A :: L) * ((A :: L).map sq).prod) • 1 := by
          rw [List.map_cons, List.prod_cons]
          simp only [pairs]
          rw [pow_add, smul_smul]
          congr 1
          ring

/-- Entrywise conjugation distributes over a matrix product. -/
theorem map_starRingEnd_mul (A B : Matrix n n ℂ) :
    (A * B).map (starRingEnd ℂ) = A.map (starRingEnd ℂ) * B.map (starRingEnd ℂ) := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

/-- Entrywise conjugation of a family product is the product of the
conjugation eigenvalues times the product itself. -/
theorem map_starRingEnd_prod {δ : Matrix n n ℂ → ℂ} :
    ∀ L : List (Matrix n n ℂ),
      (∀ A ∈ L, A.map (starRingEnd ℂ) = δ A • A) →
      L.prod.map (starRingEnd ℂ) = (L.map δ).prod • L.prod
  | [], _ => by
    ext i j
    by_cases h : i = j <;> simp [h]
  | A :: L, h => by
    have hL : ∀ B ∈ L, B.map (starRingEnd ℂ) = δ B • B :=
      fun B hB => h B (List.mem_cons_of_mem A hB)
    have hA : A.map (starRingEnd ℂ) = δ A • A := h A List.mem_cons_self
    calc (A :: L).prod.map (starRingEnd ℂ)
        = (A * L.prod).map (starRingEnd ℂ) := by rw [List.prod_cons]
      _ = A.map (starRingEnd ℂ) * L.prod.map (starRingEnd ℂ) := map_starRingEnd_mul A L.prod
      _ = (δ A • A) * ((L.map δ).prod • L.prod) := by
          rw [hA, map_starRingEnd_prod L hL]
      _ = ((A :: L).map δ).prod • (A :: L).prod := by
          rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.smul_mul,
            Matrix.mul_smul, smul_smul]

/-- **The family `B Bbar` sign.** For a pairwise anticommuting family with
square scalars `sq` and conjugation eigenvalues `δ`, the product `B`
satisfies `B * conj(B) = ((∏ δ) * (-1) ^ (pairs) * (∏ sq)) • 1`. -/
theorem prod_mul_map_starRingEnd_prod {sq δ : Matrix n n ℂ → ℂ}
    (L : List (Matrix n n ℂ)) (hnd : L.Nodup)
    (hanti : ∀ A ∈ L, ∀ B ∈ L, A ≠ B → A * B = -(B * A))
    (hsq : ∀ A ∈ L, A * A = sq A • 1)
    (hconj : ∀ A ∈ L, A.map (starRingEnd ℂ) = δ A • A) :
    L.prod * L.prod.map (starRingEnd ℂ)
      = ((L.map δ).prod * (-1 : ℂ) ^ pairs L * (L.map sq).prod) • 1 := by
  rw [map_starRingEnd_prod L hconj, Matrix.mul_smul,
    prod_sq_of_pairwise L hnd hanti hsq, smul_smul]
  congr 1
  ring

end GppWhichWayForwardFamilySigns
