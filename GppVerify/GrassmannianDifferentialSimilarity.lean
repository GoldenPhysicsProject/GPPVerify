import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.GrassmannianJacobian

namespace GppGrassmannianDifferentialSimilarity

open GppGrassmannianJacobian

/-- Row-major coordinate map for left multiplication `X -> A X`. -/
def P (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![a, 0, b, 0;
     0, a, 0, b;
     c, 0, d, 0;
     0, c, 0, d]

/-- Denominator-cleared inverse coordinate map, corresponding to left
multiplication by `adj(A)`. -/
def Q (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![d, 0, -b, 0;
     0, d, 0, -b;
     -c, 0, a, 0;
     0, -c, 0, a]

/-- Universal tangent operator `X -> X epsilon - epsilon tr X`. -/
def L : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1, 0, 0;
     0, 0, 0, -1;
     1, 0, 0, 0;
     0, 0, 1, 0]

theorem L_pow_four_eq_one :
    L * L * (L * L) = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [L, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
    norm_num

/-- `Q` and `P` multiply to the determinant scale. -/
theorem Q_mul_P_eq_D_smul_one (a b c d : ℝ) :
    Q a b c d * P a b c d
      = (a * d - b * c) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [Q, P, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
    ring

/-- The reverse product has the same determinant scale. -/
theorem P_mul_Q_eq_D_smul_one (a b c d : ℝ) :
    P a b c d * Q a b c d
      = (a * d - b * c) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [Q, P, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
    ring

/-- Core conjugacy/intertwining identity: `N P = D P L`. -/
theorem N_mul_P_eq_D_smul_P_mul_L (a b c d : ℝ) :
    N a b c d * P a b c d
      = (a * d - b * c) • (P a b c d * L) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [N, P, L, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

theorem N_mulVec_P_mulVec (a b c d : ℝ) (x : Fin 4 → ℝ) :
    N a b c d *ᵥ (P a b c d *ᵥ x)
      = (a * d - b * c) • (P a b c d *ᵥ (L *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, N_mul_P_eq_D_smul_P_mul_L]
  simp [Matrix.mulVec_mulVec]

end GppGrassmannianDifferentialSimilarity
