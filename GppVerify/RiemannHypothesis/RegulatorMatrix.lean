import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# The regulator matrix `A_ε = ε·I + w wᵀ`: determinant and inverse

Source: Astra, GPP-bridge `work/2026-10-22_astra_torus_regulator_limit.md` (Gaussian Poisson summation
over `ℤ^N` with `A_ε = ε I + w wᵀ`, `det A_ε = ε^{N−1}(ε + |w|²)`, and the dual quadratic form
`lᵀ A_ε⁻¹ l = |l_⊥|²/ε + |l_∥|²/(ε + |w|²)`). Daniel Toupin / Golden Physics Project, with AI
assistance from Astra (statement) and Claude Code (formalization).

For `ε ≠ 0` and `w : Fin n → ℝ` (with `s = w ⬝ w`), `regulator_mul_inv` shows that
`regMat ε w = ε I + w wᵀ` has the explicit right inverse
`regInv ε w = ε⁻¹ (I − (ε + s)⁻¹ w wᵀ)` when `ε + s ≠ 0`. (This is the Sherman–Morrison form from
which Astra's dual quadratic form `lᵀ A_ε⁻¹ l = |l_⊥|²/ε + |l_∥|²/(ε + |w|²)` follows.)

**Scope.** The explicit inverse only. The determinant formula `det A_ε = ε^{n−1}(ε + |w|²)`, the
quadratic-form splitting along `w`, the Gaussian Poisson summation on `ℤ^N`, the irrationality
statement (no nonzero integer vector is parallel to `(log p_i)`), the limit
`ε^{(N−1)/2} Z_ε(t) → (π/t)^{N/2}/|w|` and the idele-class-group discussion are not formalized. No
claim about RH.
-/

set_option autoImplicit false

open Matrix

namespace GppRegulatorMatrix

variable {n : ℕ}

/-- The matrix `ε I + w wᵀ`. -/
def regMat (ε : ℝ) (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ε • (1 : Matrix (Fin n) (Fin n) ℝ) + vecMulVec w w

/-- Its explicit inverse. -/
noncomputable def regInv (ε : ℝ) (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ε⁻¹ • ((1 : Matrix (Fin n) (Fin n) ℝ) - (ε + w ⬝ᵥ w)⁻¹ • vecMulVec w w)

/-- `P = w wᵀ` satisfies `P * P = (w ⬝ w) • P`. -/
theorem vecMulVec_self_mul (w : Fin n → ℝ) :
    vecMulVec w w * vecMulVec w w = (w ⬝ᵥ w) • vecMulVec w w := by
  rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]

/-- The explicit inverse is a right inverse. -/
theorem regulator_mul_inv {ε : ℝ} (w : Fin n → ℝ) (hε : ε ≠ 0) (hs : ε + w ⬝ᵥ w ≠ 0) :
    regMat ε w * regInv ε w = 1 := by
  have hPP := vecMulVec_self_mul w
  unfold regMat regInv
  generalize vecMulVec w w = P at hPP ⊢
  generalize w ⬝ᵥ w = s at hPP hs ⊢
  rw [Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_sub,
    Matrix.mul_one, Matrix.mul_smul, hPP]
  match_scalars
  · field_simp
  · field_simp
    ring

end GppRegulatorMatrix
