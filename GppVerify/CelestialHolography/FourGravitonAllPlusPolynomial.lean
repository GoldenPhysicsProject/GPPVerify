import Mathlib.Tactic

/-!
# Three-box polynomial collapse in the four-graviton all-plus sector

The massless `mu^8` scalar-box residue appearing in the four-point all-plus
gravity representation carries the quadratic polynomial

  P(x,y) = 2 x^2 + 2 y^2 + x y.

This file formalizes only the exact kinematic algebra: when the four-point
Mandelstam variables satisfy `s+t+u=0`, the three channel polynomials collapse to

  P(s,t) + P(u,s) + P(t,u) = 7/2 (s^2+t^2+u^2).

No amplitude, KLT, state-sum, integral-reduction, or dimension-shift statement is
assumed or asserted here.
-/

namespace GppFourGravitonAllPlusPolynomial

/-- Quadratic residue polynomial of one massless `mu^8` box. -/
def P (x y : ℝ) : ℝ := 2 * x ^ 2 + 2 * y ^ 2 + x * y

/-- Exact three-channel polynomial collapse at massless four-point kinematics. -/
theorem three_box_polynomial_collapse
    (s t u : ℝ) (hstu : s + t + u = 0) :
    P s t + P u s + P t u =
      (7 / 2 : ℝ) * (s ^ 2 + t ^ 2 + u ^ 2) := by
  unfold P
  have hu : u = -s - t := by linarith
  rw [hu]
  ring

/-- The normalization used by the `mu^8` box residue consequently collapses from
three channel-dependent `1/840` terms to the symmetric `1/240` coefficient. -/
theorem three_box_residue_normalization
    (s t u : ℝ) (hstu : s + t + u = 0) :
    (P s t + P u s + P t u) / 840 =
      (s ^ 2 + t ^ 2 + u ^ 2) / 240 := by
  rw [three_box_polynomial_collapse s t u hstu]
  ring

end GppFourGravitonAllPlusPolynomial

#print axioms GppFourGravitonAllPlusPolynomial.three_box_polynomial_collapse
#print axioms GppFourGravitonAllPlusPolynomial.three_box_residue_normalization
