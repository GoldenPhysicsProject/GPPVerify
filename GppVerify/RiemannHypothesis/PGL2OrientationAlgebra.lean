import GppVerify.RiemannHypothesis.ArithmeticConformalKinematics
import Mathlib.Tactic

/-!
# PGL(2,R) orientation algebra for the 1D conformal thread

For a real Mobius transformation represented by a matrix

  [[a,b],[c,d]],

its derivative away from the pole has the sign of the determinant because

  f'(x) = (ad-bc)/(cx+d)^2.

Moreover replacing the matrix by a nonzero scalar multiple multiplies the
determinant by a strictly positive square.  Thus determinant sign is invariant
under the scalar equivalence defining PGL(2,R), and separates its
orientation-preserving and orientation-reversing components.

This is only the exact finite algebra behind the proposed 1D conformal sign
channel.  It does not construct PGL(2,R) as a quotient, a local operator algebra,
an OPE, crossing symmetry, or a full CFT.
-/

namespace GppPGL2Orientation

/-- Determinant of a real 2-by-2 representative. -/
def det2 (a b c d : ℝ) : ℝ := a * d - b * c

/-- The derivative factor of the associated Mobius map, away from a pole. -/
def mobiusDerivativeFactor (a b c d x : ℝ) : ℝ :=
  det2 a b c d / (c * x + d) ^ 2

/-- A positive-determinant representative acts orientation-preservingly wherever defined. -/
theorem mobiusDerivativeFactor_pos
    {a b c d x : ℝ}
    (hdet : 0 < det2 a b c d)
    (hpole : c * x + d ≠ 0) :
    0 < mobiusDerivativeFactor a b c d x := by
  unfold mobiusDerivativeFactor
  exact div_pos hdet (sq_pos_of_ne_zero hpole)

/-- A negative-determinant representative acts orientation-reversingly wherever defined. -/
theorem mobiusDerivativeFactor_neg
    {a b c d x : ℝ}
    (hdet : det2 a b c d < 0)
    (hpole : c * x + d ≠ 0) :
    mobiusDerivativeFactor a b c d x < 0 := by
  unfold mobiusDerivativeFactor
  exact div_neg_of_neg_of_pos hdet (sq_pos_of_ne_zero hpole)

/-- Scalar change of a projective representative multiplies its determinant by a square. -/
theorem det2_scale (r a b c d : ℝ) :
    det2 (r * a) (r * b) (r * c) (r * d) = r ^ 2 * det2 a b c d := by
  unfold det2
  ring

/-- Therefore positive determinant is invariant under nonzero projective rescaling. -/
theorem det2_scale_pos_iff
    {r a b c d : ℝ} (hr : r ≠ 0) :
    0 < det2 (r * a) (r * b) (r * c) (r * d) ↔
      0 < det2 a b c d := by
  rw [det2_scale]
  exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hr))

/-- Likewise negative determinant is invariant under nonzero projective rescaling. -/
theorem det2_scale_neg_iff
    {r a b c d : ℝ} (hr : r ≠ 0) :
    det2 (r * a) (r * b) (r * c) (r * d) < 0 ↔
      det2 a b c d < 0 := by
  rw [det2_scale]
  exact (mul_neg_iff_of_pos_left (sq_pos_of_ne_zero hr))

/-- The sign channel is independent of position: for two regular points the derivative
factors have positive product, so their signs agree. -/
theorem derivative_sign_constant_on_regular_points
    {a b c d x y : ℝ}
    (hdet : det2 a b c d ≠ 0)
    (hx : c * x + d ≠ 0)
    (hy : c * y + d ≠ 0) :
    0 < mobiusDerivativeFactor a b c d x *
      mobiusDerivativeFactor a b c d y := by
  unfold mobiusDerivativeFactor
  have hdetSq : 0 < (det2 a b c d) ^ 2 := sq_pos_of_ne_zero hdet
  have hxSq : 0 < (c * x + d) ^ 2 := sq_pos_of_ne_zero hx
  have hySq : 0 < (c * y + d) ^ 2 := sq_pos_of_ne_zero hy
  rw [div_mul_div_comm]
  exact div_pos (by simpa [pow_two] using hdetSq) (mul_pos hxSq hySq)

end GppPGL2Orientation

#print axioms GppPGL2Orientation.mobiusDerivativeFactor_pos
#print axioms GppPGL2Orientation.mobiusDerivativeFactor_neg
#print axioms GppPGL2Orientation.det2_scale_pos_iff
#print axioms GppPGL2Orientation.det2_scale_neg_iff
#print axioms GppPGL2Orientation.derivative_sign_constant_on_regular_points
