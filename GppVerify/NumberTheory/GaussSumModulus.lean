import Mathlib.NumberTheory.GaussSum

/-!
# Gauss sum modulus formula for quadratic characters

Source: Tate's-thesis lecture notes (Warwick "tateweek4" notes, epsilon-factor discussion
around line 219/233) and Tate's thesis itself — the classical fact that a Gauss sum for a
nontrivial quadratic character has absolute value `√(card R)`, underlying the algebra of
local epsilon factors in the functional equation.

Real infrastructure, not sourced from a specific Golden Physics Project paper: derived
here from Mathlib's existing `gaussSum_sq` (`gaussSum χ ψ ^ 2 = χ(-1) · card R`), since a
quadratic character always sends `-1` to `1` or `-1` (never `0`, as `-1` is a unit in any
field), so `‖χ(-1)‖ = 1` regardless of sign, giving `‖gaussSum χ ψ‖² = card R`.
-/

namespace GppGaussSumModulus

variable {R : Type*} [Field R] [Fintype R]

/-- **Gauss sum modulus formula**: for a nontrivial quadratic multiplicative character `χ`
    and a primitive additive character `ψ` (both valued in `ℂ`) on a finite field `R`, the
    Gauss sum has absolute value `√(card R)`. -/
theorem gaussSum_norm_eq_sqrt_card (χ : MulChar R ℂ) (hχ₁ : χ ≠ 1) (hχ₂ : χ.IsQuadratic)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card R) := by
  have hsq : gaussSum χ ψ ^ 2 = χ (-1) * (Fintype.card R : ℂ) := gaussSum_sq hχ₁ hχ₂ hψ
  have hself : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul]
    have hR : (-1 : R) * (-1) = 1 := by ring
    rw [hR]
    exact map_one χ
  have hne : χ (-1) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hself
    exact zero_ne_one hself
  have hval : χ (-1) = 1 ∨ χ (-1) = -1 := (hχ₂ (-1)).resolve_left hne
  have hnorm_chi : ‖χ (-1)‖ = 1 := by rcases hval with h | h <;> simp [h]
  have hnormsq : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card R : ℝ) := by
    have h := congrArg norm hsq
    simp only [norm_pow, norm_mul, hnorm_chi, one_mul] at h
    exact_mod_cast h
  rw [← hnormsq, Real.sqrt_sq (norm_nonneg _)]

end GppGaussSumModulus
