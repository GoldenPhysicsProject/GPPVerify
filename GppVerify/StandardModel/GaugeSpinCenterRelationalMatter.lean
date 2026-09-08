import Mathlib.Tactic
import GppVerify.StandardModel.CPTMatterOrientationSpine
import GppVerify.CelestialHolography.SpinProductCenterTimeOrientation

/-!
# Gauge sign times relative spin-center orientation

The U(1)/Wilson-line analysis gives an internal conjugation sign `c`.  Independently, the
factorized Lorentz/null-spinor geometry has two central signs `sL,sR`, whose only vector-level
character is

  t = sL sR.

The diagonal spin center `(-1,-1)` is invisible on vectors, while either one-sided center
flip reverses the oriented null-vector representative and hence reverses `t`.

Combining the two structures gives the relational source/matter character

  m = c t = c sL sR.

Thus charge dualization `c -> -c` accompanied by reversal of the relative spin-center
orientation `t -> -t` leaves `m` invariant.  Charge dualization alone, or orientation
reversal alone, changes `m`.

This is the exact finite algebra sought by the project's `q*t` intuition, now with `t`
derived from the center of the doubled spinor factorization rather than inserted as a
free Boolean label.  The physical statement that this character exhausts all locally
observable particle/antiparticle information remains a QFT hypothesis to be tested.
-/

namespace GppGaugeSpinCenterRelationalMatter

open GppSpinProductCenterTimeOrientation

/-- Spinorial orientation sign seen by the vector representation. -/
def spinTimeSign (sL sR : ℝ) : ℝ := vectorCenterCharacter sL sR

/-- Combined gauge/orientation character. -/
def matterCharacter3 (c sL sR : ℝ) : ℝ := c * spinTimeSign sL sR

/-- The three-sign character is simply the product `c*sL*sR`. -/
theorem matterCharacter3_eq_product (c sL sR : ℝ) :
    matterCharacter3 c sL sR = c*sL*sR := by
  rfl

/-- The diagonal spin-center deck sign is invisible even before charge is considered. -/
theorem diagonal_spin_deck_invisible (c sL sR : ℝ) :
    matterCharacter3 c (-sL) (-sR) = matterCharacter3 c sL sR := by
  simp [matterCharacter3, spinTimeSign, vectorCenterCharacter]

/-- Gauge conjugation plus LEFT implementation of worldline/vector reversal leaves the
relational matter character unchanged. -/
theorem gauge_flip_plus_left_orientation_flip_invariant (c sL sR : ℝ) :
    matterCharacter3 (-c) (-sL) sR = matterCharacter3 c sL sR := by
  simp [matterCharacter3, spinTimeSign, vectorCenterCharacter]

/-- Gauge conjugation plus RIGHT implementation of the same orientation reversal gives the
same invariant result. -/
theorem gauge_flip_plus_right_orientation_flip_invariant (c sL sR : ℝ) :
    matterCharacter3 (-c) sL (-sR) = matterCharacter3 c sL sR := by
  simp [matterCharacter3, spinTimeSign, vectorCenterCharacter]

/-- The two spinorial lifts of orientation reversal are physically identical at the level
of this character; they differ only by the diagonal center. -/
theorem two_orientation_lifts_agree_after_gauge_flip (c sL sR : ℝ) :
    matterCharacter3 (-c) (-sL) sR =
      matterCharacter3 (-c) sL (-sR) := by
  simp [matterCharacter3, spinTimeSign, vectorCenterCharacter]

/-- Charge dualization by itself changes the relational class. -/
theorem gauge_flip_only_changes_character (c sL sR : ℝ) :
    matterCharacter3 (-c) sL sR = - matterCharacter3 c sL sR := by
  simp [matterCharacter3, spinTimeSign, vectorCenterCharacter]

/-- Reversing the relative spin-center orientation by itself also changes the class. -/
theorem left_orientation_flip_only_changes_character (c sL sR : ℝ) :
    matterCharacter3 c (-sL) sR = - matterCharacter3 c sL sR := by
  simp [matterCharacter3, spinTimeSign, vectorCenterCharacter]

/-- Same for the right lift. -/
theorem right_orientation_flip_only_changes_character (c sL sR : ℝ) :
    matterCharacter3 c sL (-sR) = - matterCharacter3 c sL sR := by
  simp [matterCharacter3, spinTimeSign, vectorCenterCharacter]

end GppGaugeSpinCenterRelationalMatter
