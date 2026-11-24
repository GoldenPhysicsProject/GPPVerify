import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Rat.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

* `ftheta_coeff_bounds`, `ftheta_coeff_not_int` (Codex, PR #11 6389930457): the would-be local
  point-count coefficient of `F_θ(s) = ξ(s − θ) ξ(s + θ)` at `p = 2`, `θ = 1/4`, is
  `c = 2^{1/4} + 2^{−1/4}`, and `2 < c < 3`. So `c` is not an integer, whereas a genuine
  Hasse–Weil coefficient such as `#P¹(F_p) = p + 1` is. This is a named integrality hypothesis that
  `F_θ` fails at `p = 2` with no zero input.

So the functional-equation-type duality alone does not put the spectrum on the circle `|λ| = √q`;
the missing ingredient is a genuinely constructed polarization / height.

**Scope.** A finite rational countermodel and one real-number inequality. `F_bad` is abstract
and is not the geometric Frobenius of any curve. Nothing here constructs a height for ζ; the
integrality gate does not show that ζ has on-line zeros and does not exclude non-geometric
shifts. Nothing bears on RH or BSD.
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

/-- **The `F_θ` coefficient at `p = 2`, `θ = 1/4`, lies strictly between `2` and `3`.** -/
theorem ftheta_coeff_bounds :
    2 < (2 : ℝ) ^ (1 / 4 : ℝ) + (2 : ℝ) ^ (-(1 / 4) : ℝ) ∧
      (2 : ℝ) ^ (1 / 4 : ℝ) + (2 : ℝ) ^ (-(1 / 4) : ℝ) < 3 := by
  set x := (2 : ℝ) ^ (1 / 4 : ℝ) with hx
  have hxpos : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (2 : ℝ) ^ (-(1 / 4) : ℝ) = x⁻¹ := by
    rw [Real.rpow_neg (by norm_num)]
  have h4 : x ^ 4 = 2 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hx1 : 1 < x := by
    by_contra h; push Not at h
    have : x ^ 4 ≤ 1 := pow_le_one₀ hxpos.le h
    linarith
  have hx2 : x < 5 / 4 := by
    by_contra h; push Not at h
    have : (5 / 4 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) h 4
    norm_num at this; linarith
  rw [hinv]
  have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hxpos.ne'
  constructor
  · have : 2 * x < x * x + 1 := by nlinarith
    have h2 : x + x⁻¹ = (x * x + 1) / x := by field_simp
    rw [h2, lt_div_iff₀ hxpos]; linarith
  · have : x * x + 1 < 3 * x := by nlinarith
    have h2 : x + x⁻¹ = (x * x + 1) / x := by field_simp
    rw [h2, div_lt_iff₀ hxpos]; linarith

/-- **Integrality gate.** The `F_θ` coefficient `2^{1/4} + 2^{−1/4}` is not an integer. -/
theorem ftheta_coeff_not_int (n : ℤ) :
    (2 : ℝ) ^ (1 / 4 : ℝ) + (2 : ℝ) ^ (-(1 / 4) : ℝ) ≠ n := by
  intro h
  obtain ⟨h1, h2⟩ := ftheta_coeff_bounds
  rw [h] at h1 h2
  have : (2 : ℤ) < n := by exact_mod_cast h1
  have : n < 3 := by exact_mod_cast h2
  omega

end GppDualityHeight
