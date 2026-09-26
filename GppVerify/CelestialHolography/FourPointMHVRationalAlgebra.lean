import Mathlib.Tactic

/-!
# Four-point adjacent-MHV rational cancellation algebra

After the D-dimensional scalar cuts are reduced, the FDH rational remainder has
box and bubble pieces

  `-(1/6) * (2 i Q)`

and

  `-(1/6) * (i Q * 2(2s-3t)/(3t))`.

The spinor-helicity derivation of the second coefficient relation is kept in the
Discovery record; this file formalizes the exact final cancellation once that relation
has been supplied.
-/

namespace GppFourPointMHVRationalAlgebra

/-- The scalar coefficient multiplying the common helicity phase `i Q` after
combining the `mu^4` box and `mu^2` bubble rational weights. -/
def rationalScalar (s t : ℂ) : ℂ :=
  -(1 / 6) * 2 - (1 / 6) * (2 * (2 * s - 3 * t) / (3 * t))

/-- Exact cancellation of the `3t` pieces:
`-1/3 - (2s-3t)/(9t) = -2s/(9t)`. -/
theorem rationalScalar_eq {s t : ℂ} (ht : t ≠ 0) :
    rationalScalar s t = -(2 * s) / (9 * t) := by
  unfold rationalScalar
  field_simp [ht]
  ring

/-- Coefficient-level version with an arbitrary common complex helicity factor `Q`. -/
theorem box_add_bubble_eq_compact
    {s t Q : ℂ} (ht : t ≠ 0) :
    -(1 / 6) * (2 * Complex.I * Q)
      - (1 / 6) * (Complex.I * Q * (2 * (2 * s - 3 * t) / (3 * t)))
    = -(2 * Complex.I / 9) * (s / t) * Q := by
  field_simp [ht]
  ring

/-- With `Xi = -Q`, the same remainder is `+(2 i/9)(s/t) Xi`. -/
theorem compact_eq_Xi
    {s t Q Xi : ℂ} (ht : t ≠ 0) (hXi : Xi = -Q) :
    -(2 * Complex.I / 9) * (s / t) * Q
      = (2 * Complex.I / 9) * (s / t) * Xi := by
  rw [hXi]
  ring

end GppFourPointMHVRationalAlgebra

#print axioms GppFourPointMHVRationalAlgebra.rationalScalar_eq
#print axioms GppFourPointMHVRationalAlgebra.box_add_bubble_eq_compact
#print axioms GppFourPointMHVRationalAlgebra.compact_eq_Xi
