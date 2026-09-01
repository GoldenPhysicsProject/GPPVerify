import GppVerify.QuantumInformation.ChoiMatrix
import GppVerify.QuantumInformation.HalfFlipMatrix

open scoped ComplexOrder Matrix

/-!
# Proposition 2.2, complete: the transpose map on M_2(ℂ) is not completely positive

## Golden Physics Project — GPPVerify
## Lean 4 | Mathlib v4.33.1

This file connects the two general/specific pieces built elsewhere in this session:

* `GppChoiMatrix` (`ChoiMatrix.lean`): the general Choi-matrix / complete-positivity
  framework, independent of any specific map.
* `GppHalfFlipMatrix` (`HalfFlipMatrix.lean`): `SWAP` and the fact that it is not
  positive semidefinite (`swap_not_posSemidef`).

Here we define the transpose map on `M_2(ℂ)` as an actual `ℂ`-linear map, prove its Choi
matrix is *exactly* `SWAP` (an unconditional finite computation — no reindexing needed,
verified by hand before writing this proof), and conclude the full, unconditional form
of Proposition 2.2: the transpose map on `M_2(ℂ)` is not completely positive. This
finally retires `HalfFlipProposition.lean`'s `open_no_enactment` stub for the concrete `d = 2`
case as a real theorem rather than a documented gap.
-/

namespace GppHalfFlipMatrix

/-- The transpose map on `M_2(ℂ)`, as the `ℂ`-linear map `X ↦ Xᵀ`. -/
def transposeMap : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := Matrix.transpose
  map_add' := Matrix.transpose_add
  map_smul' := Matrix.transpose_smul

/-- **Choi(transpose) = SWAP** (Proposition 2.2): both sides reduce, entry by entry, to
    the same product of Kronecker deltas — an exact finite computation, no `sorry`, no
    numerical approximation. -/
theorem choiMatrix_transposeMap_eq_SWAP :
    GppChoiMatrix.ChoiMatrix transposeMap = SWAP := by
  funext p q
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
    simp (config := { decide := true }) [GppChoiMatrix.ChoiMatrix, GppChoiMatrix.matrixMapTensor,
      GppChoiMatrix.maxEntangled, transposeMap, SWAP, Matrix.replicateCol_apply,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Fin.sum_univ_one,
      Prod.ext_iff]

/-- **Proposition 2.2, complete**: the transpose map on `M_2(ℂ)` is not completely
    positive — the full, unconditional statement. -/
theorem transposeMap_not_completelyPositive :
    ¬ GppChoiMatrix.CompletelyPositive transposeMap := by
  apply GppChoiMatrix.not_completelyPositive_of_not_posSemidef_choiMatrix
  rw [choiMatrix_transposeMap_eq_SWAP]
  exact swap_not_posSemidef

end GppHalfFlipMatrix
