import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Rat.Star

/-!
# Exact duality does not locate spectral roots; a positive height does

Source: Codex, GPP-bridge PR #11 comment 6389906209 (Discovery2 PR #20, "ζ on S²" / BSD sewing
interface). Daniel Toupin / Golden Physics Project, with AI assistance from Codex (statement) and
Claude Code (formalization).

Take `q = 16` and the symplectic form `J = [[0, 1], [−1, 0]]` over `ℚ`.

* `bad_dual`, `good_dual`: both `F_bad = diag(8, 2)` and `F_good = [[0, −16], [1, 0]]` satisfy the
  exact mirror duality `Fᵀ J F = q J`.
* `bad_no_height`: `F_bad` admits **no** positive definite `H` with `Fᵀ H F = q H`; the `(0,0)`
  entry forces `64 h₀₀ = 16 h₀₀`, so `h₀₀ = 0`. (Its eigenvalues `8, 2` do not have modulus
  `√q = 4`.)
* `good_height`: `F_good` admits the positive definite height `H = diag(1, 16)`.

So the functional-equation-type duality alone does not put the spectrum on the circle `|λ| = √q`;
the missing ingredient is a genuinely constructed polarization / height.

**Scope.** A finite rational countermodel. `F_bad` is abstract and is not the geometric Frobenius
of any curve. Nothing here constructs a height for ζ, and nothing bears on RH or BSD.
-/

open Matrix

namespace GppDualityHeight

/-- The symplectic form `J`. -/
def J : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; -1, 0]

/-- The non-geometric "Frobenius" `diag(8, 2)`. -/
def Fbad : Matrix (Fin 2) (Fin 2) ℚ := !![8, 0; 0, 2]

/-- A Frobenius with eigenvalues of modulus `4`. -/
def Fgood : Matrix (Fin 2) (Fin 2) ℚ := !![0, -16; 1, 0]

/-- The height for `Fgood`. -/
def Hgood : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 16]

theorem bad_dual : Fbadᵀ * J * Fbad = (16 : ℚ) • J := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Fbad, J, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem good_dual : Fgoodᵀ * J * Fgood = (16 : ℚ) • J := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Fgood, J, Matrix.mul_apply, Fin.sum_univ_two]

/-- **No positive height for `F_bad`.** -/
theorem bad_no_height (H : Matrix (Fin 2) (Fin 2) ℚ) (hH : H.PosDef)
    (hF : Fbadᵀ * H * Fbad = (16 : ℚ) • H) : False := by
  have h00 := congrFun (congrFun hF 0) 0
  simp [Fbad, Matrix.mul_apply, Fin.sum_univ_two] at h00
  have hpos := hH.diag_pos (i := 0)
  linarith

/-- **`F_good` has the positive height `diag(1, 16)`.** -/
theorem good_height : Hgood.PosDef ∧ Fgoodᵀ * Hgood * Fgood = (16 : ℚ) • Hgood := by
  refine ⟨?_, ?_⟩
  · have : Hgood = Matrix.diagonal ![1, 16] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [this, Matrix.posDef_diagonal_iff]
    intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Fgood, Hgood, Matrix.mul_apply, Fin.sum_univ_two]

end GppDualityHeight
