import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation

/-!
# Exact universal-NOT fidelity algebra for qubits

This file isolates the finite-dimensional calculation behind Proposition 4.1(c) of the
half-flip paper.  No Bloch-sphere parametrization is needed.

For every 2×2 complex matrix `A`, the Pauli conjugation identity is

  σx A σx + σy A σy + σz A σz = 2 Tr(A) I - A.

Hence for a pure qubit density matrix `rho` (`Tr rho = 1`, `rho^2 = rho`), the equal
Pauli mixture is

  E(rho) = (2 I - rho) / 3.

The orthogonal pure-state projector is `I-rho`; its overlap with `E(rho)` is exactly
`2/3`.
-/

namespace GppUniversalNot

open Matrix

abbrev Qubit := Fin 2
abbrev QMat := Matrix Qubit Qubit ℂ

noncomputable def sigmaX : QMat := !![0, 1; 1, 0]
noncomputable def sigmaY : QMat := !![0, -Complex.I; Complex.I, 0]
noncomputable def sigmaZ : QMat := !![1, 0; 0, -1]

noncomputable def tr2 (A : QMat) : ℂ := A 0 0 + A 1 1

noncomputable def pauliSum (A : QMat) : QMat :=
  sigmaX * A * sigmaX + sigmaY * A * sigmaY + sigmaZ * A * sigmaZ

noncomputable def universalNot (A : QMat) : QMat := (3 : ℂ)⁻¹ • pauliSum A

/-- The Pauli conjugation identity on `M₂(ℂ)`. -/
theorem pauliSum_eq (A : QMat) :
    pauliSum A = (2 * tr2 A) • (1 : QMat) - A := by
  have hI_sandwich (z : ℂ) : Complex.I * (z * Complex.I) = -z := by
    calc
      Complex.I * (z * Complex.I) = (Complex.I * Complex.I) * z := by ring
      _ = (-1 : ℂ) * z := by rw [Complex.I_mul_I]
      _ = -z := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliSum, sigmaX, sigmaY, sigmaZ, tr2, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, hI_sandwich] <;>
    ring

/-- For a normalized qubit state, the equal Pauli mixture is `(2I-rho)/3`. -/
theorem universalNot_eq_of_trace_one (rho : QMat) (htr : tr2 rho = 1) :
    universalNot rho = (3 : ℂ)⁻¹ • ((2 : ℂ) • (1 : QMat) - rho) := by
  rw [universalNot, pauliSum_eq, htr]
  norm_num

/-- Two-by-two trace is linear under addition. -/
theorem tr2_add (A B : QMat) : tr2 (A + B) = tr2 A + tr2 B := by
  simp [tr2]
  ring

/-- Two-by-two trace is linear under subtraction. -/
theorem tr2_sub (A B : QMat) : tr2 (A - B) = tr2 A - tr2 B := by
  simp [tr2]
  ring

/-- Two-by-two trace of the identity is two. -/
theorem tr2_one : tr2 (1 : QMat) = 2 := by
  norm_num [tr2]

/-- Two-by-two trace respects scalar multiplication. -/
theorem tr2_smul (c : ℂ) (A : QMat) : tr2 (c • A) = c * tr2 A := by
  simp [tr2]
  ring

/-- Exact product identity used in the pure-state fidelity calculation. -/
theorem orthogonal_product_identity (rho : QMat) :
    (1 - rho) * ((2 : ℂ) • (1 : QMat) - rho) =
      (2 : ℂ) • (1 : QMat) - (3 : ℂ) • rho + rho * rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    ring_nf

/-- Exact overlap with the orthogonal projector for a pure normalized qubit state. -/
theorem universalNot_orthogonal_fidelity
    (rho : QMat)
    (htr : tr2 rho = 1)
    (hpure : rho * rho = rho) :
    tr2 ((1 - rho) * universalNot rho) = (2 : ℂ) / 3 := by
  rw [universalNot_eq_of_trace_one rho htr]
  rw [Matrix.mul_smul]
  rw [tr2_smul]
  rw [orthogonal_product_identity, hpure]
  rw [tr2_add, tr2_sub, tr2_smul, tr2_smul, tr2_one, htr]
  norm_num

end GppUniversalNot

#print axioms GppUniversalNot.pauliSum_eq
#print axioms GppUniversalNot.universalNot_orthogonal_fidelity
