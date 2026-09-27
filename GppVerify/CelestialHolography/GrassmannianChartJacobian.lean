import Mathlib.Tactic

/-!
# Exact fourth-power identity for the Gr(2,4) opposite-chart Jacobian

On the big-cell overlap, write

  D = a*d - b*c

and consider the transition

  F(a,b,c,d) = (-b/D, a/D, -d/D, c/D).

Its Jacobian is `D⁻²` times the polynomial matrix encoded below as
`jacobianScaled`.  The key exact identity is

  jacobianScaled^4 = D^4 I.

Consequently, when `D ≠ 0`, the actual Jacobian satisfies `J_F^4 = D⁻⁴ I`.
This replaces the incorrect stronger claim that the four-coordinate Jacobian
squares to `-I` at `D=1`.
-/

namespace GppGrassmannianChartJacobian

/-- Plücker determinant on the standard big cell. -/
def detScale (a b c d : ℂ) : ℂ := a * d - b * c

/-- Polynomial numerator of `D^2 * dF` for the opposite-chart transition.
The coordinates are ordered `(a,b,c,d)`. -/
def jacobianScaled (a b c d : ℂ) (v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![
    b * d * v 0 - a * d * v 1 - b^2 * v 2 + a * b * v 3,
    -b * c * v 0 + a * c * v 1 + a * b * v 2 - a^2 * v 3,
    d^2 * v 0 - c * d * v 1 - b * d * v 2 + b * c * v 3,
    -c * d * v 0 + c^2 * v 1 + a * d * v 2 - a * c * v 3
  ]

/-- The scaled chart Jacobian has exact order four up to the fourth power of
the Plücker determinant.  This is a denominator-free polynomial identity. -/
theorem jacobianScaled_fourth (a b c d : ℂ) (v : Fin 4 → ℂ) :
    jacobianScaled a b c d
      (jacobianScaled a b c d
        (jacobianScaled a b c d
          (jacobianScaled a b c d v)))
      = fun i => (detScale a b c d)^4 * v i := by
  funext i
  fin_cases i <;> simp [jacobianScaled, detScale] <;> ring

/-- At unit determinant the fourth iterate is literally the identity. -/
theorem jacobianScaled_fourth_of_det_one
    (a b c d : ℂ) (hD : detScale a b c d = 1) (v : Fin 4 → ℂ) :
    jacobianScaled a b c d
      (jacobianScaled a b c d
        (jacobianScaled a b c d
          (jacobianScaled a b c d v))) = v := by
  rw [jacobianScaled_fourth, hD]
  funext i
  simp

end GppGrassmannianChartJacobian

#print axioms GppGrassmannianChartJacobian.jacobianScaled_fourth
#print axioms GppGrassmannianChartJacobian.jacobianScaled_fourth_of_det_one
