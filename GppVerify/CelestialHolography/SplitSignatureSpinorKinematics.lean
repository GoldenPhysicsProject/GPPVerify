import Mathlib.Tactic

/-!
# Split-signature spinor kinematics

In signature `(2,2)`, real null momenta admit a factorization by two independent
real two-component spinors.  This file records only the exact algebra needed by
the celestial cut program:

* the spinor-factorized momentum is null for the split quadratic form;
* the split bilinear factorizes into an angle bracket times a square bracket.

No analytic continuation or amplitude normalization is assumed here.
-/

namespace GppSplitSignatureSpinorKinematics

/-- A real four-vector in split signature. -/
structure SplitMomentum where
  p0 : ℝ
  p1 : ℝ
  p2 : ℝ
  p3 : ℝ

/-- Quadratic form of signature `(2,2)` in the convention `(+,-,+,-)`. -/
def q22 (p : SplitMomentum) : ℝ :=
  p.p0 ^ 2 - p.p1 ^ 2 + p.p2 ^ 2 - p.p3 ^ 2

/-- Associated symmetric bilinear form. -/
def dot22 (p q : SplitMomentum) : ℝ :=
  p.p0 * q.p0 - p.p1 * q.p1 + p.p2 * q.p2 - p.p3 * q.p3

/-- Real spinor factorization of a split-signature null momentum.
The first spinor is `(a,b)` and the second is `(c,d)`. -/
def fromSpinors (a b c d : ℝ) : SplitMomentum where
  p0 := (a * c + b * d) / 2
  p1 := (a * d + b * c) / 2
  p2 := (a * d - b * c) / 2
  p3 := (a * c - b * d) / 2

/-- The undotted `SL(2,R)` antisymmetric bracket. -/
def angleBracket (a b e f : ℝ) : ℝ := a * f - b * e

/-- The dotted `SL(2,R)` antisymmetric bracket. -/
def squareBracket (c d g h : ℝ) : ℝ := c * h - d * g

/-- The spinor-factorized momentum reconstructs the rank-one bispinor entries. -/
theorem fromSpinors_rank_one_coordinates (a b c d : ℝ) :
    let p := fromSpinors a b c d
    p.p0 + p.p3 = a * c ∧
    p.p0 - p.p3 = b * d ∧
    p.p1 + p.p2 = a * d ∧
    p.p1 - p.p2 = b * c := by
  dsimp [fromSpinors]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Every real bispinor outer product is null in split signature. -/
theorem fromSpinors_null (a b c d : ℝ) :
    q22 (fromSpinors a b c d) = 0 := by
  simp [q22, fromSpinors]
  ring

/-- Exact split-signature spinor-helicity factorization:
`2 p·q = <lambda mu> [lambda_tilde mu_tilde]`. -/
theorem two_mul_dot22_eq_angle_mul_square
    (a b c d e f g h : ℝ) :
    2 * dot22 (fromSpinors a b c d) (fromSpinors e f g h) =
      angleBracket a b e f * squareBracket c d g h := by
  simp [dot22, fromSpinors, angleBracket, squareBracket]
  ring

/-- Hence orthogonality follows from either vanishing spinor bracket. -/
theorem dot22_eq_zero_of_angle_eq_zero
    {a b c d e f g h : ℝ}
    (hang : angleBracket a b e f = 0) :
    dot22 (fromSpinors a b c d) (fromSpinors e f g h) = 0 := by
  have h := two_mul_dot22_eq_angle_mul_square a b c d e f g h
  rw [hang] at h
  norm_num at h ⊢
  linarith

/-- Likewise for a vanishing dotted bracket. -/
theorem dot22_eq_zero_of_square_eq_zero
    {a b c d e f g h : ℝ}
    (hsq : squareBracket c d g h = 0) :
    dot22 (fromSpinors a b c d) (fromSpinors e f g h) = 0 := by
  have h := two_mul_dot22_eq_angle_mul_square a b c d e f g h
  rw [hsq] at h
  norm_num at h ⊢
  linarith

end GppSplitSignatureSpinorKinematics

#print axioms GppSplitSignatureSpinorKinematics.fromSpinors_null
#print axioms GppSplitSignatureSpinorKinematics.two_mul_dot22_eq_angle_mul_square
#print axioms GppSplitSignatureSpinorKinematics.dot22_eq_zero_of_angle_eq_zero
#print axioms GppSplitSignatureSpinorKinematics.dot22_eq_zero_of_square_eq_zero
