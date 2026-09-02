import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.GrassmannianComplexDifferential

/-!
# Exact Grassmannian-to-Dirac quarter-cycle intertwiner

The universal complex Grassmannian tangent operator `L` is four-dimensional.
It splits transparently into an elliptic two-plane, spanned by the symmetric
traceless Pauli directions, where `L²=-1`, and a complementary scalar/
antisymmetric two-plane where `L²=+1`.

The rest Dirac quarter-cycle `Uq=-i sigma1` is an exact quotient of `L`:
`Phi L = Uq Phi`.  `Phi` kills the scalar/antisymmetric sector and is onto the
two-component Dirac space.  This is an exact algebraic intertwiner; a claim
that Nature physically selects this quotient requires the separate physical
dictionary developed in the companion mass/clock bridge.
-/

namespace GppGrassmannianDiracIntertwiner

open GppGrassmannianComplexDifferential

/-- Rest-Dirac quarter-cycle `-i σ₁`. -/
def Uq : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I;
     -Complex.I, 0]

/-- Quotient/intertwiner.  On a row-major matrix `X=[[a,b],[c,d]]`, this is
`(i(a-d), b+c)`: the diagonal-difference and symmetric-off-diagonal
coordinates, i.e. the symmetric traceless two-plane with a fixed phase on the
first coordinate. -/
def Phi : Matrix (Fin 2) (Fin 4) ℂ :=
  !![Complex.I, 0, 0, -Complex.I;
     0, 1, 1, 0]

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

theorem Phi_surjective (y : Fin 2 → ℂ) :
    ∃ x : Fin 4 → ℂ, Phi *ᵥ x = y := by
  refine ⟨R *ᵥ y, ?_⟩
  rw [← Matrix.mulVec_mulVec, Phi_mul_R_eq_one]
  simp

/-! ## Canonical two-plane decomposition -/

def eSigma3 : Fin 4 → ℂ := ![1,0,0,-1]
def eSigma1 : Fin 4 → ℂ := ![0,1,1,0]
def eScalar : Fin 4 → ℂ := ![1,0,0,1]
def eEpsilon : Fin 4 → ℂ := ![0,1,-1,0]

/-- Elliptic sector: `σ3 -> σ1`. -/
theorem L_eSigma3 : L *ᵥ eSigma3 = eSigma1 := by
  ext i; fin_cases i <;> norm_num [L,eSigma3,eSigma1,Matrix.mulVec,Fin.sum_univ_four]

/-- Elliptic sector: `σ1 -> -σ3`; therefore `L²=-1` on this two-plane. -/
theorem L_eSigma1 : L *ᵥ eSigma1 = -eSigma3 := by
  ext i; fin_cases i <;> norm_num [L,eSigma3,eSigma1,Matrix.mulVec,Fin.sum_univ_four]

/-- Hyperbolic sector: scalar direction maps to minus the epsilon direction. -/
theorem L_eScalar : L *ᵥ eScalar = -eEpsilon := by
  ext i; fin_cases i <;> norm_num [L,eScalar,eEpsilon,Matrix.mulVec,Fin.sum_univ_four]

/-- Hyperbolic sector: epsilon maps to minus the scalar direction; therefore
`L²=+1` on this complementary two-plane. -/
theorem L_eEpsilon : L *ᵥ eEpsilon = -eScalar := by
  ext i; fin_cases i <;> norm_num [L,eScalar,eEpsilon,Matrix.mulVec,Fin.sum_univ_four]

/-- The quotient kills the scalar direction. -/
theorem Phi_eScalar_zero : Phi *ᵥ eScalar = 0 := by
  ext i; fin_cases i <;> simp [Phi,eScalar,Matrix.mulVec,Fin.sum_univ_four]

/-- The quotient kills the antisymmetric epsilon direction. -/
theorem Phi_eEpsilon_zero : Phi *ᵥ eEpsilon = 0 := by
  ext i; fin_cases i <;> simp [Phi,eEpsilon,Matrix.mulVec,Fin.sum_univ_four]

/-- On `σ3`, the quotient is the first Dirac coordinate (up to `2i`). -/
theorem Phi_eSigma3 : Phi *ᵥ eSigma3 = ![2 * Complex.I,0] := by
  ext i; fin_cases i <;> simp [Phi,eSigma3,Matrix.mulVec,Fin.sum_univ_four] <;> ring

/-- On `σ1`, the quotient is the second Dirac coordinate (up to `2`). -/
theorem Phi_eSigma1 : Phi *ᵥ eSigma1 = ![0,2] := by
  ext i; fin_cases i <;> norm_num [Phi,eSigma1,Matrix.mulVec,Fin.sum_univ_four]

/-- The `+1` Grassmannian mode is killed by the quotient. -/
theorem Phi_vOne_zero : Phi *ᵥ vOne = 0 := by
  ext i
  fin_cases i <;> norm_num [Phi, vOne, Matrix.mulVec, Fin.sum_univ_four]

/-- The `-1` Grassmannian mode is killed by the quotient. -/
theorem Phi_vNegOne_zero : Phi *ᵥ vNegOne = 0 := by
  ext i
  fin_cases i <;> norm_num [Phi, vNegOne, Matrix.mulVec, Fin.sum_univ_four]

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
