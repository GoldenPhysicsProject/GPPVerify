import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.GrassmannianComplexDifferential

/-!
# Exact Grassmannian-to-Dirac quarter-cycle intertwiner

The universal complex Grassmannian tangent operator `L` is four-dimensional
with fourth-root spectrum.  The rest Dirac quarter-cycle at
`t = π/(2 ω_C)` is `Uq = -i σ₁`, a two-dimensional operator with eigenvalues
`±i`.

The explicit rank-two map `Phi` below satisfies

    Phi L = Uq Phi.

Thus the Dirac quarter-cycle is an exact quotient representation of the
Grassmannian order-four tangent dynamics.  The `±1` Grassmannian modes lie in
the kernel, while the `±i` modes descend to the two Dirac energy-axis modes.
This is a purely algebraic intertwining theorem; identifying this quotient as
the physical mechanism of spin remains a physics interpretation beyond the
matrix identity itself.
-/

namespace GppGrassmannianDiracIntertwiner

open GppGrassmannianComplexDifferential

/-- Rest-Dirac quarter-cycle `-i σ₁`. -/
def Uq : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I;
     -Complex.I, 0]

/-- Quotient/intertwiner from the four Grassmannian tangent coordinates to the
two-component rest Dirac state. -/
def Phi : Matrix (Fin 2) (Fin 4) ℂ :=
  !![Complex.I, 0, 0, -Complex.I;
     0, 1, 1, 0]

/-- Exact intertwining relation. -/
theorem Phi_mul_L_eq_Uq_mul_Phi :
    Phi * L = Uq * Phi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [Phi, Uq, L, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four,
       Complex.I_mul_I] <;>
    ring

/-- A concrete right inverse, proving that `Phi` is onto. -/
def R : Matrix (Fin 4) (Fin 2) ℂ :=
  !![-Complex.I, 0;
     0, 1;
     0, 0;
     0, 0]

theorem Phi_mul_R_eq_one :
    Phi * R = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [Phi, R, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply,
       Complex.I_mul_I] <;>
    ring

/-- `Phi` is surjective at the vector level. -/
theorem Phi_surjective (y : Fin 2 → ℂ) :
    ∃ x : Fin 4 → ℂ, Phi *ᵥ x = y := by
  refine ⟨R *ᵥ y, ?_⟩
  rw [← Matrix.mulVec_mulVec, Phi_mul_R_eq_one]
  simp

/-- The `+1` Grassmannian mode is killed by the quotient. -/
theorem Phi_vOne_zero : Phi *ᵥ vOne = 0 := by
  ext i
  fin_cases i <;>
    norm_num [Phi, vOne, Matrix.mulVec, Fin.sum_univ_four]

/-- The `-1` Grassmannian mode is killed by the quotient. -/
theorem Phi_vNegOne_zero : Phi *ᵥ vNegOne = 0 := by
  ext i
  fin_cases i <;>
    norm_num [Phi, vNegOne, Matrix.mulVec, Fin.sum_univ_four]

/-- The `+i` Grassmannian mode descends to a nonzero Dirac mode. -/
theorem Phi_vI :
    Phi *ᵥ vI = ![2 * Complex.I, -2 * Complex.I] := by
  ext i
  fin_cases i <;>
    simp [Phi, vI, Matrix.mulVec, Fin.sum_univ_four, Complex.I_mul_I] <;>
    ring

/-- The `-i` Grassmannian mode descends to the complementary nonzero Dirac mode. -/
theorem Phi_vNegI :
    Phi *ᵥ vNegI = ![2 * Complex.I, 2 * Complex.I] := by
  ext i
  fin_cases i <;>
    simp [Phi, vNegI, Matrix.mulVec, Fin.sum_univ_four, Complex.I_mul_I] <;>
    ring

/-- The image of the `+i` mode is a `+i` eigenvector of the Dirac quarter-cycle. -/
theorem Uq_Phi_vI :
    Uq *ᵥ (Phi *ᵥ vI) = Complex.I • (Phi *ᵥ vI) := by
  rw [← Matrix.mulVec_mulVec, ← Phi_mul_L_eq_Uq_mul_Phi,
      Matrix.mulVec_mulVec, L_vI, Matrix.mulVec_smul]

/-- The image of the `-i` mode is a `-i` eigenvector of the Dirac quarter-cycle. -/
theorem Uq_Phi_vNegI :
    Uq *ᵥ (Phi *ᵥ vNegI) = (-Complex.I) • (Phi *ᵥ vNegI) := by
  rw [← Matrix.mulVec_mulVec, ← Phi_mul_L_eq_Uq_mul_Phi,
      Matrix.mulVec_mulVec, L_vNegI, Matrix.mulVec_smul]

/-- Applying two Dirac quarter-cycles gives the spinorial deck sign `-1`. -/
theorem Uq_sq_eq_neg_one :
    Uq * Uq = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [Uq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
       Complex.I_mul_I] <;>
    ring

/-- Four Dirac quarter-cycles close. -/
theorem Uq_four_eq_one :
    Uq * Uq * (Uq * Uq) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Uq_sq_eq_neg_one]
  simp

end GppGrassmannianDiracIntertwiner
