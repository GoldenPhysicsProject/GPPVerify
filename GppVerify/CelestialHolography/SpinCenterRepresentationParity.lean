import Mathlib.Tactic

/-!
# Center parity of (a,b) spin representations

For the complexified four-dimensional spin group, tensor/spinor representations are graded
by the number of left and right fundamental spinor factors.  At the level needed here,
encode a bidegree `(a,b)` by the center character

  chi_(a,b)(sL,sR) = sL^a sR^b,

where `sL,sR` are the two central signs.

This elementary bookkeeping sharply separates several structures:

* vector/tangent representation `(1,1)`: a one-sided center flip gives `-1`, while the
  diagonal `(-1,-1)` is invisible;
* left/right Weyl fermions `(1,0)` and `(0,1)`: odd under their own center;
* chiral gauge curvature `(2,0)` or `(0,2)`: center-even;
* chiral gravitational Weyl curvature `(4,0)` or `(0,4)`: center-even.

Thus the relative center can carry an oriented-vector/worldline sign without changing the
integer-spin field strengths/curvatures.  Factor exchange, separately, swaps `(a,b)` with
`(b,a)` and therefore exchanges the two gauge/gravity chiralities.

This is pure representation-parity algebra, not a dynamical theorem.
-/

namespace GppSpinCenterRepresentationParity

/-- Center character of a spinor bidegree `(a,b)`. -/
def centerCharacter (a b : ℕ) (sL sR : ℝ) : ℝ := sL^a * sR^b

/-- Diagonal central reversal acts by parity of the total spinor degree. -/
theorem diagonal_center_character (a b : ℕ) :
    centerCharacter a b (-1) (-1) = (-1 : ℝ)^(a+b) := by
  simp [centerCharacter, pow_add]
  ring

/-- Factor exchange swaps the two bidegrees and the two center signs. -/
theorem factor_exchange_character (a b : ℕ) (sL sR : ℝ) :
    centerCharacter b a sR sL = centerCharacter a b sL sR := by
  simp [centerCharacter, mul_comm]

/-- Vector representation `(1,1)`: diagonal center invisible, either one-sided flip odd. -/
theorem vector_center_package :
    centerCharacter 1 1 (-1) (-1) = 1 ∧
    centerCharacter 1 1 (-1) 1 = -1 ∧
    centerCharacter 1 1 1 (-1) = -1 := by
  norm_num [centerCharacter]

/-- Left Weyl fermion is odd under the left center. -/
theorem left_fermion_center_odd : centerCharacter 1 0 (-1) 1 = -1 := by
  norm_num [centerCharacter]

/-- Right Weyl fermion is odd under the right center. -/
theorem right_fermion_center_odd : centerCharacter 0 1 1 (-1) = -1 := by
  norm_num [centerCharacter]

/-- Chiral spin-one field strength `(2,0)` is center-even. -/
theorem left_gauge_curvature_center_even : centerCharacter 2 0 (-1) 1 = 1 := by
  norm_num [centerCharacter]

/-- Opposite spin-one chirality is likewise center-even. -/
theorem right_gauge_curvature_center_even : centerCharacter 0 2 1 (-1) = 1 := by
  norm_num [centerCharacter]

/-- Self-dual Weyl curvature spinor `(4,0)` is center-even. -/
theorem left_weyl_curvature_center_even : centerCharacter 4 0 (-1) 1 = 1 := by
  norm_num [centerCharacter]

/-- Anti-self-dual Weyl curvature spinor `(0,4)` is center-even. -/
theorem right_weyl_curvature_center_even : centerCharacter 0 4 1 (-1) = 1 := by
  norm_num [centerCharacter]

/-- The mixed Ricci representation `(2,2)` is even under either center. -/
theorem mixed_ricci_center_even :
    centerCharacter 2 2 (-1) 1 = 1 ∧ centerCharacter 2 2 1 (-1) = 1 := by
  norm_num [centerCharacter]

/-- Chiral factor exchange swaps the two gravitational Weyl bidegrees. -/
theorem googly_bidegree_exchange : (4,0) = ((0,4).2,(0,4).1) := by
  rfl

/-- And similarly swaps the two gauge-curvature bidegrees. -/
theorem gauge_bidegree_exchange : (2,0) = ((0,2).2,(0,2).1) := by
  rfl

end GppSpinCenterRepresentationParity
