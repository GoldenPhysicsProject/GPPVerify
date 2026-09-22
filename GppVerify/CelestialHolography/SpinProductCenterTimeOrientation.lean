import Mathlib.Tactic
import GppVerify.CelestialHolography.FlatInfinityCelestialFactorization
import GppVerify.StandardModel.OrientationMassTime

/-!
# Relative spin-product center as the orientation sign of a null vector

For a factorized null momentum

  p = lambda tensor lambdatilde,

the two chiral spinor factors each carry their own central sign.  Acting by signs
`sL,sR in {+1,-1}` gives

  (lambda,lambdatilde) -> (sL lambda, sR lambdatilde),
  p -> (sL sR) p.

Consequently the diagonal center `(-1,-1)` is invisible on the vector representation,
while either single central flip sends `p -> -p`.  Thus

  ({+/-1}_L x {+/-1}_R) / diag({+/-1}) ~= {+/-1}

and its nontrivial character is the PRODUCT of the two spin-center signs.

For a real time-oriented null cone, `p` and `-p` lie on the same projective null line but
carry opposite ray/worldline orientation (future versus past once a time orientation is
chosen).  The latter geometric interpretation is external to the finite split-signature
algebra proved here.

This gives a precise candidate for the project's previously abstract worldline-orientation
bit `t`: not "left SL(2) versus right SL(2)", but the *relative central sign* of the two
spinor factors.  It is exactly the sign forgotten when an oriented null vector is
projectivized to an unoriented null line.
-/

namespace GppSpinProductCenterTimeOrientation

open GppFlatInfinityCelestialFactorization
open GppOrientationMassTime

/-- The central sign action on a spinor factor. -/
def centerScale (s : ℝ) (lambda : Spinor2) : Spinor2 := scale2 s lambda

/-- The induced character on the vector representation is the product of the two signs. -/
def vectorCenterCharacter (sL sR : ℝ) : ℝ := sL * sR

/-- General center-action formula on a factorized null momentum. -/
theorem nullMomentum_center_action (sL sR : ℝ) (lambda lambdatilde : Spinor2) :
    nullMomentum (centerScale sL lambda) (centerScale sR lambdatilde) =
      scaleM2 (vectorCenterCharacter sL sR) (nullMomentum lambda lambdatilde) := by
  simpa [centerScale, vectorCenterCharacter] using
    nullMomentum_biscaling sL sR lambda lambdatilde

/-- The diagonal central sign `(-1,-1)` acts trivially on the vector/null momentum. -/
theorem diagonal_center_is_vector_invisible (lambda lambdatilde : Spinor2) :
    nullMomentum (centerScale (-1) lambda) (centerScale (-1) lambdatilde) =
      nullMomentum lambda lambdatilde := by
  rw [nullMomentum_center_action]
  rcases nullMomentum lambda lambdatilde with ⟨a,b,c,d⟩
  norm_num [vectorCenterCharacter, scaleM2]

/-- Flipping only the left spin-center sign reverses the oriented null-vector representative. -/
theorem left_center_flip_reverses_vector (lambda lambdatilde : Spinor2) :
    nullMomentum (centerScale (-1) lambda) lambdatilde =
      scaleM2 (-1) (nullMomentum lambda lambdatilde) := by
  simpa [centerScale] using nullMomentum_biscaling (-1) 1 lambda lambdatilde

/-- Flipping only the right spin-center sign does the same. -/
theorem right_center_flip_reverses_vector (lambda lambdatilde : Spinor2) :
    nullMomentum lambda (centerScale (-1) lambdatilde) =
      scaleM2 (-1) (nullMomentum lambda lambdatilde) := by
  simpa [centerScale] using nullMomentum_biscaling 1 (-1) lambda lambdatilde

/-- The two single flips are indistinguishable downstairs on the vector representation. -/
theorem either_half_center_flip_same_vector (lambda lambdatilde : Spinor2) :
    nullMomentum (centerScale (-1) lambda) lambdatilde =
      nullMomentum lambda (centerScale (-1) lambdatilde) := by
  rw [left_center_flip_reverses_vector, right_center_flip_reverses_vector]

/-- Simultaneously changing both spin-center signs leaves the relative/vector sign invariant. -/
theorem diagonal_center_preserves_character (sL sR : ℝ) :
    vectorCenterCharacter (-sL) (-sR) = vectorCenterCharacter sL sR := by
  simp [vectorCenterCharacter]

/-- Either single center flip reverses the relative/vector sign. -/
theorem single_center_flip_reverses_character (sL sR : ℝ) :
    vectorCenterCharacter (-sL) sR = - vectorCenterCharacter sL sR ∧
    vectorCenterCharacter sL (-sR) = - vectorCenterCharacter sL sR := by
  simp [vectorCenterCharacter]

/-- The spin-product center quotient has exactly the same finite product law as the
orientation character used in the charge/worldline quotient. -/
theorem spin_center_product_matches_relational_character (sL sR : ℝ) :
    vectorCenterCharacter sL sR = relationalCharacter sL sR := by
  rfl

end GppSpinProductCenterTimeOrientation
