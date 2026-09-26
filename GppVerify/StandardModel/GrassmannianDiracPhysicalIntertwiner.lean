import Mathlib.Tactic
import GppVerify.GrassmannianComplexDifferential
import GppVerify.StandardModel.GrassmannianDiracIntertwiner

/-!
# The actual Grassmannian Jacobian descends to the Dirac quarter-cycle

The universal theorem `Phi L = Uq Phi` can be transported back from tangent
coordinates `X` to the actual chart coordinates `H=A X`.  With `Q` the
adjugate coordinate map, define `Psi_A = Phi Q_A`.  Then the polynomial
Jacobian numerator obeys

    Psi_A N_A = D Uq Psi_A.

Since the actual Jacobian is `J_A=N_A/D^2`, on the big cell `D != 0` this
becomes

    Psi_A J_A = D^{-1} Uq Psi_A.

Thus the actual Grassmannian differential has an exact two-component quotient
whose order-four part is the rest-Dirac quarter-cycle and whose scale is the
inverse chart determinant.  This is an algebraic representation theorem; the
physical mass interpretation of `|D|` is supplied separately by
`GrassmannianPhysicalMass.lean`.
-/

namespace GppGrassmannianDiracPhysicalIntertwiner

open GppGrassmannianComplexDifferential
open GppGrassmannianDiracIntertwiner

/-- A-dependent quotient map from actual chart tangent coordinates to the
Dirac two-state coordinates. -/
def Psi (a b c d : ℂ) : Matrix (Fin 2) (Fin 4) ℂ :=
  Phi * Q a b c d

/-- The key denominator-free transport identity `Q N = D L Q`. -/
theorem QN_eq_D_LQ (a b c d : ℂ) :
    Q a b c d * N a b c d = D a b c d • (L * Q a b c d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [Q, N, D, L, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

/-- Polynomial form of the actual Grassmannian-to-Dirac intertwiner. -/
theorem Psi_N_eq_D_Uq_Psi (a b c d : ℂ) :
    Psi a b c d * N a b c d
      = D a b c d • (Uq * Psi a b c d) := by
  rw [Psi, Matrix.mul_assoc, QN_eq_D_LQ]
  rw [Matrix.mul_smul]
  rw [← Matrix.mul_assoc, Phi_mul_L_eq_Uq_mul_Phi]
  simp [Psi, Matrix.mul_assoc]

/-- Actual Jacobian matrix `N/D²`. -/
def Jmat (a b c d : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (D a b c d)⁻¹ ^ 2 • N a b c d

/-- Main theorem: on the big cell, the actual Grassmannian differential
quotients to `D^{-1} Uq`. -/
theorem Psi_Jmat_eq_invD_Uq_Psi
    (a b c d : ℂ) (hD : D a b c d ≠ 0) :
    Psi a b c d * Jmat a b c d
      = (D a b c d)⁻¹ • (Uq * Psi a b c d) := by
  rw [Jmat, Matrix.mul_smul, Psi_N_eq_D_Uq_Psi]
  ext i j
  simp [Matrix.smul_apply]
  field_simp [hD]
  ring

/-- Vector-level form of the main intertwiner. -/
theorem Psi_Jmat_mulVec
    (a b c d : ℂ) (hD : D a b c d ≠ 0) (v : Fin 4 → ℂ) :
    Psi a b c d *ᵥ (Jmat a b c d *ᵥ v)
      = (D a b c d)⁻¹ • (Uq *ᵥ (Psi a b c d *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, Psi_Jmat_eq_invD_Uq_Psi a b c d hD]
  simp [Matrix.mulVec_mulVec]

/-- `Psi_A` is onto whenever `D != 0`: the quotient really has two
independent Dirac coordinates, not a smaller image. -/
theorem Psi_surjective
    (a b c d : ℂ) (hD : D a b c d ≠ 0) (y : Fin 2 → ℂ) :
    ∃ v : Fin 4 → ℂ, Psi a b c d *ᵥ v = y := by
  obtain ⟨x, hx⟩ := Phi_surjective y
  refine ⟨(D a b c d)⁻¹ • (P a b c d *ᵥ x), ?_⟩
  simp only [Psi, Matrix.mulVec_mulVec, Matrix.mulVec_smul]
  rw [← Matrix.mulVec_mulVec, QP]
  ext i
  simp [hx]
  field_simp [hD]

end GppGrassmannianDiracPhysicalIntertwiner
