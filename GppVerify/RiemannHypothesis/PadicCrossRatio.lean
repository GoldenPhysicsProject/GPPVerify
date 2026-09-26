import GppVerify.RiemannHypothesis.PadicMobiusConformal
import Mathlib.Tactic

/-!
# p-adic Möbius cross-ratio invariance

The affine boundary of the p-adic projective line has the same exact four-point
Möbius invariant as an ordinary one-dimensional conformal boundary.  This is a
substantive CFT kinematic datum: after two-point covariance, the nontrivial
coordinate dependence of a scalar four-point function can be reduced to a cross
ratio.

No CFT axiom is used.  The theorem is a direct field identity over Mathlib's
`Padic p`.
-/

namespace GppPadicCrossRatio

open GppPadicMobiusConformal

variable (p : ℕ) [Fact p.Prime]

/-- The affine cross ratio `(x₁₂ x₃₄)/(x₁₃ x₂₄)`. -/
noncomputable def crossRatio (x1 x2 x3 x4 : Padic p) : Padic p :=
  ((x1 - x2) * (x3 - x4)) / ((x1 - x3) * (x2 - x4))

/-- **Exact p-adic conformal four-point invariant.**  A nondegenerate fractional
linear transformation preserves the cross ratio wherever the affine chart and
cross-ratio denominators are defined. -/
theorem crossRatio_mobius
    {a b c d x1 x2 x3 x4 : Padic p}
    (hdet : mobiusDet p a b c d ≠ 0)
    (h1 : c * x1 + d ≠ 0) (h2 : c * x2 + d ≠ 0)
    (h3 : c * x3 + d ≠ 0) (h4 : c * x4 + d ≠ 0)
    (h13 : x1 - x3 ≠ 0) (h24 : x2 - x4 ≠ 0) :
    crossRatio p
        (mobius p a b c d x1) (mobius p a b c d x2)
        (mobius p a b c d x3) (mobius p a b c d x4) =
      crossRatio p x1 x2 x3 x4 := by
  unfold crossRatio
  rw [mobius_sub p h1 h2, mobius_sub p h3 h4,
      mobius_sub p h1 h3, mobius_sub p h2 h4]
  field_simp [hdet, h1, h2, h3, h4, h13, h24]
  ring

end GppPadicCrossRatio

#print axioms GppPadicCrossRatio.crossRatio_mobius
