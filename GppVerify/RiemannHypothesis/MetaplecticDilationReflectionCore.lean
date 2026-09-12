import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Metaplectic quarter-turn / dilation-reflection core

The analytic Weil/metaplectic representation has two structural operations that are central
both to the arithmetic-principal-series programme and to the project's orientation work:

* a Fourier quarter-turn, whose square is parity and whose fourth power is the identity;
* a centered dilation generator, whose sign is reversed by Fourier conjugation while its
  square is preserved.

This file isolates the exact finite `2 x 2` algebraic skeleton.  Put

    J = [[0,-1],[1,0]],      D = [[1,0],[0,-1]].

Then

    J^2 = -1,       J^4 = 1,
    J D = - D J,    D^2 = 1,

so the first-order orientation `D` is odd under the quarter-turn while the positive square
`D^2` is even.  This is the same order-four algebra as a spinorial lift and as the
Grassmannian `tau^2=-1`, `tau^4=1` structure already formalized elsewhere in GPPVerify.

The theorem here is only the finite algebraic core.  The analytic statement
`F A F^{-1} = -A` for the unitary Fourier transform `F` and centered dilation generator
`A=-i(x d/dx + 1/2)` on `L^2(R)` requires Fourier/Sobolev domain machinery and is not
silently asserted by these matrix identities.
-/

namespace GppMetaplecticDilationReflectionCore

/-- Real quarter-turn matrix, the finite skeleton of the Fourier/metaplectic `S` element. -/
def quarterTurn : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0,-1;
     1, 0]

/-- Two-orientation first-order grading, the finite skeleton of centered dilation sign. -/
def dilationSign : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0;
     0,-1]

/-- A quarter-turn squares to the negative central element. -/
theorem quarterTurn_sq_neg_one :
    quarterTurn * quarterTurn = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quarterTurn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- Consequently the quarter-turn closes after four applications. -/
theorem quarterTurn_four_one :
    quarterTurn * quarterTurn * quarterTurn * quarterTurn =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [quarterTurn_sq_neg_one]
  simp

/-- The first-order dilation sign squares to the positive identity. -/
theorem dilationSign_sq_one :
    dilationSign * dilationSign = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dilationSign, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- The quarter-turn reverses the first-order orientation: `J D = - D J`. -/
theorem quarterTurn_anticommutes_dilationSign :
    quarterTurn * dilationSign = -(dilationSign * quarterTurn) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quarterTurn, dilationSign, Matrix.mul_apply, Fin.sum_univ_two]

/-- The positive square is invariant under the quarter-turn. -/
theorem quarterTurn_commutes_positive_square :
    quarterTurn * (dilationSign * dilationSign) =
      (dilationSign * dilationSign) * quarterTurn := by
  rw [dilationSign_sq_one]
  simp

/-- Capstone package: order-four lift, reflection-odd first-order sign, positive even square. -/
theorem metaplectic_orientation_package :
    quarterTurn * quarterTurn = -(1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    quarterTurn * quarterTurn * quarterTurn * quarterTurn =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    quarterTurn * dilationSign = -(dilationSign * quarterTurn) ∧
    dilationSign * dilationSign = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact ⟨quarterTurn_sq_neg_one, quarterTurn_four_one,
    quarterTurn_anticommutes_dilationSign, dilationSign_sq_one⟩

end GppMetaplecticDilationReflectionCore
