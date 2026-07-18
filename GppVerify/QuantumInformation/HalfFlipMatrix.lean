import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped ComplexOrder

/-!
# The Half-Flip Obstruction: the Finite Matrix Core
# Lean 4 | GPPVerify
# Author: Daniel Toupin | Golden Physics Project

## Statement

The transpose map on M_2(ℂ) has Choi operator equal to the SWAP operator on
ℂ² ⊗ ℂ² (Proposition 2.2 of "The Half-Flip Proposition"): SWAP(|k⟩⊗|l⟩) =
|l⟩⊗|k⟩. This file proves, as an exact finite matrix-vector computation
with no axiom, no `sorry`, and no numerical approximation, that SWAP has
a negative eigenvalue: the antisymmetric singlet vector ψ, with
ψ(0,1) = 1, ψ(1,0) = -1, and ψ = 0 elsewhere, satisfies SWAP *ᵥ ψ = -ψ
and ψ ≠ 0.

We then close the loop all the way to Mathlib's own `Matrix.PosSemidef`
predicate (`swap_not_posSemidef`): SWAP is *not* positive semidefinite,
on the nose, not merely "has a negative eigenvalue" left for the reader to
connect. Since Choi's theorem says a linear map Φ : M_2(ℂ) → M_2(ℂ) is
completely positive iff its Choi matrix is positive semidefinite, and
Choi(transpose) = SWAP (Proposition 2.2), this is the exact finite
obstruction behind "the transpose is not completely positive."

The identification of SWAP with Choi(transpose), and the general
statement of Choi's theorem itself (which needs a Kronecker-product
formalization of the Choi matrix for a general linear map, not attempted
here), remain recorded in comments only; the theorems below are
self-contained, unconditional claims about the matrix SWAP and the
vector ψ, provable without appeal to either.
-/

namespace GppHalfFlipMatrix

/-- The SWAP operator on ℂ² ⊗ ℂ², indexed by Fin 2 × Fin 2: row p, column
    q, entry 1 iff q is p with its two coordinates exchanged. Equivalently,
    SWAP sends the basis vector at (k,l) to the basis vector at (l,k). -/
def SWAP : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => if q = (p.2, p.1) then 1 else 0

/-- The antisymmetric singlet vector: ψ(0,1) = 1, ψ(1,0) = -1, else 0. -/
def psi : (Fin 2 × Fin 2) → ℂ :=
  fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0

/-- SWAP *ᵥ ψ = -ψ: the singlet is an eigenvector of SWAP with eigenvalue
    -1, proved by exact matrix-vector multiplication at each of the 4
    basis points. -/
theorem SWAP_mulVec_psi : SWAP.mulVec psi = -psi := by
  funext p
  obtain ⟨i, j⟩ := p
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [SWAP, psi, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The singlet vector is nonzero. -/
theorem psi_ne_zero : psi ≠ 0 := by
  intro h
  have h01 : psi (0, 1) = (0 : (Fin 2 × Fin 2) → ℂ) (0, 1) := congrFun h (0, 1)
  simp [psi] at h01

/-- Packaging: SWAP has eigenvalue -1, witnessed by the nonzero vector ψ.
    A positive semidefinite matrix has no negative eigenvalue, so this is
    the exact finite-dimensional obstruction behind Choi(transpose) = SWAP
    not being completely positive. -/
theorem SWAP_has_negative_eigenvector :
    ∃ v : (Fin 2 × Fin 2) → ℂ, v ≠ 0 ∧ SWAP.mulVec v = (-1 : ℂ) • v := by
  refine ⟨psi, psi_ne_zero, ?_⟩
  rw [SWAP_mulVec_psi]
  exact (neg_one_smul ℂ psi).symm

/-- **SWAP is not positive semidefinite**, on the nose (via Mathlib's own
    `Matrix.PosSemidef`), not merely "has a negative eigenvalue." If SWAP
    were positive semidefinite, its defining inequality applied to ψ would
    force `0 ≤ Re⟨ψ, SWAP ψ⟩ = Re⟨ψ, -ψ⟩ = -Re⟨ψ, ψ⟩`, i.e. `⟨ψ,ψ⟩ ≤ 0`;
    but `⟨ψ, ψ⟩ > 0` since `ψ ≠ 0`. Contradiction. This is exactly the
    finite obstruction Choi's theorem turns into "the transpose is not
    completely positive." -/
theorem swap_not_posSemidef : ¬ SWAP.PosSemidef := by
  intro hPSD
  have hle : 0 ≤ RCLike.re (dotProduct (star psi) (SWAP.mulVec psi)) :=
    hPSD.re_dotProduct_nonneg psi
  rw [SWAP_mulVec_psi, dotProduct_neg, map_neg] at hle
  have hpos : 0 < dotProduct (star psi) psi :=
    Matrix.dotProduct_star_self_pos_iff.mpr psi_ne_zero
  have hpos_re : 0 < RCLike.re (dotProduct (star psi) psi) := (RCLike.pos_iff.mp hpos).1
  linarith

end GppHalfFlipMatrix
