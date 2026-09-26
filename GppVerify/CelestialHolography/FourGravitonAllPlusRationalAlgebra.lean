import Mathlib.Tactic

/-!
# Four-graviton all-plus three-box polynomial collapse

The massless limit of each `mu^8` gravity box contributes the quadratic polynomial
`P(x,y) = 2x^2 + 2y^2 + xy` divided by `840`. The three inequivalent box orderings
carry `(s,t)`, `(u,s)`, `(t,u)`. This file formalizes the exact collapse to the symmetric
`(s^2+t^2+u^2)/120` coefficient after including the overall factor two in the amplitude.
-/

namespace GppFourGravitonAllPlusRationalAlgebra

/-- Appendix-D massless `mu^8` box polynomial. -/
def boxPoly (x y : ℝ) : ℝ := 2 * x ^ 2 + 2 * y ^ 2 + x * y

/-- The three channel polynomials collapse to `7/2` times the symmetric square sum. -/
theorem three_boxPoly_eq
    {s t u : ℝ} (hstu : s + t + u = 0) :
    boxPoly s t + boxPoly u s + boxPoly t u =
      (7 / 2 : ℝ) * (s ^ 2 + t ^ 2 + u ^ 2) := by
  unfold boxPoly
  nlinarith [sq_nonneg (s + t + u)]

/-- Including the factor `1/840` from each box and the overall factor `2` from the
four-point amplitude gives exactly the symmetric coefficient `1/120`. -/
theorem normalized_three_boxPoly_eq
    {s t u : ℝ} (hstu : s + t + u = 0) :
    2 * ((boxPoly s t + boxPoly u s + boxPoly t u) / 840) =
      (s ^ 2 + t ^ 2 + u ^ 2) / 120 := by
  rw [three_boxPoly_eq hstu]
  ring

end GppFourGravitonAllPlusRationalAlgebra

#print axioms GppFourGravitonAllPlusRationalAlgebra.three_boxPoly_eq
#print axioms GppFourGravitonAllPlusRationalAlgebra.normalized_three_boxPoly_eq
