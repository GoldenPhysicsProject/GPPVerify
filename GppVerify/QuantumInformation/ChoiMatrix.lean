import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped ComplexOrder Matrix

/-!
# Complete positivity and the Choi matrix, in general

## Golden Physics Project — GPPVerify
## Lean 4 | Mathlib v4.19.0

This file builds the general-purpose infrastructure needed to state and use Choi's
theorem for an *arbitrary* finite-dimensional linear map `Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ`,
using Mathlib's own `Matrix.PosSemidef`. It does not depend on any specific map (transpose,
depolarizing channel, etc.) — that specialization is done elsewhere
(`GppVerify/QuantumInformation/HalfFlipMatrix.lean`).

## Definitions

* `matrixMapTensor Φ M`: the matrix `(Φ ⊗ id_β) M`, obtained by viewing `M` as a `β × β`
  array of `n × n` blocks and applying `Φ` to each block.
* `CompletelyPositive Φ`: `Φ` maps positive semidefinite matrices to positive semidefinite
  matrices after tensoring with the identity on an auxiliary system of *any* finite
  dimension `β` — the textbook definition of complete positivity.
* `maxEntangled`: the (unnormalised) maximally entangled test state `Σᵢ|i,i⟩`, built as the
  manifestly positive semidefinite rank-one matrix `A Aᴴ` for a single-column `A`.
* `ChoiMatrix Φ`: `(Φ ⊗ id_n)` applied to `maxEntangled` — the Choi matrix of `Φ`.

## What is proved

`choiMatrix_posSemidef_of_completelyPositive`: if `Φ` is completely positive then its Choi
matrix is positive semidefinite. This is the *easy* (forward) direction of Choi's theorem —
it follows in one line from the definitions, since the Choi matrix is exactly
`(Φ ⊗ id_n)` applied to a positive semidefinite test state. The *hard* (converse) direction
of Choi's theorem — that a positive semidefinite Choi matrix already forces complete
positivity for *every* auxiliary dimension `β`, not just `β = n` — is a genuinely deeper
result (it needs an operator-sum / Kraus decomposition of `Φ` recovered from a
spectral decomposition of the Choi matrix) and is not attempted here.

The forward direction is exactly what is needed to turn "the Choi matrix is not positive
semidefinite" into "the map is not completely positive" by contraposition
(`not_completelyPositive_of_not_posSemidef_choiMatrix`), which is the shape of the argument
used for the transpose map's Choi matrix (Proposition 2.2 of "The Half-Flip Proposition").
-/

namespace GppChoiMatrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- `(Φ ⊗ id_β) M`: apply `Φ` block-wise to a matrix indexed by `n × β`, treating `M` as a
    `β × β` array of `n × n` blocks and leaving the `β` structure untouched. -/
def matrixMapTensor (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) {β : Type} [Fintype β] [DecidableEq β]
    (M : Matrix (n × β) (n × β) ℂ) : Matrix (n × β) (n × β) ℂ :=
  fun p q => Φ (Matrix.of fun k l => M (k, p.2) (l, q.2)) p.1 q.1

/-- **Complete positivity**: `Φ` maps positive semidefinite matrices to positive
    semidefinite matrices after tensoring with the identity on an auxiliary system of
    *any* finite dimension `β`. -/
def CompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  ∀ (β : Type) [Fintype β] [DecidableEq β] (M : Matrix (n × β) (n × β) ℂ),
    M.PosSemidef → (matrixMapTensor Φ M).PosSemidef

/-- The (unnormalised) maximally entangled test state `Ω = Σᵢ |i,i⟩`, as the rank-one
    positive semidefinite matrix `A Aᴴ` for the single-column matrix `A` whose one column
    is the indicator vector of the diagonal `{(i,i)}`. -/
def maxEntangled : Matrix (n × n) (n × n) ℂ :=
  Matrix.replicateCol (Fin 1) (fun p : n × n => if p.1 = p.2 then (1 : ℂ) else 0) *
    (Matrix.replicateCol (Fin 1) (fun p : n × n => if p.1 = p.2 then (1 : ℂ) else 0))ᴴ

/-- `maxEntangled` is positive semidefinite: it is manifestly of the form `A Aᴴ`. -/
theorem maxEntangled_posSemidef : (maxEntangled (n := n)).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

/-- The **Choi matrix** of `Φ`: `(Φ ⊗ id_n)` applied to the maximally entangled test
    state. -/
def ChoiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  matrixMapTensor Φ maxEntangled

/-- **Choi's theorem, forward direction**: a completely positive map has positive
    semidefinite Choi matrix. (The converse — Choi matrix PSD implies CP for every
    auxiliary dimension — is the hard direction of Choi's theorem and is not needed,
    and not proved, here.) -/
theorem choiMatrix_posSemidef_of_completelyPositive {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hΦ : CompletelyPositive Φ) : (ChoiMatrix Φ).PosSemidef :=
  hΦ n maxEntangled maxEntangled_posSemidef

/-- **Contrapositive form**: if the Choi matrix is not positive semidefinite, the map is
    not completely positive. -/
theorem not_completelyPositive_of_not_posSemidef_choiMatrix
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (h : ¬ (ChoiMatrix Φ).PosSemidef) :
    ¬ CompletelyPositive Φ :=
  fun hΦ => h (choiMatrix_posSemidef_of_completelyPositive hΦ)

end GppChoiMatrix
