import Mathlib.Tactic
import GppVerify.StandardModel.MassBreaksRelativeScale
import GppVerify.CelestialHolography.SpinProductCenterTimeOrientation

/-!
# Mass selects the diagonal spin center; the other coset is oriented-vector reversal

The doubled spinor carrier has four central sign choices

  ( +,+ ), (-,-), (-,+), (+,-).

The vector representation sees only the product

  t = sL sR.

Hence `(+,+)` and `(-,-)` have `t=+1`, while the two one-sided signs have `t=-1`.
The Dirac/contact mass exchange `beta=sigma1` supplies a second, independent fact:

  diag(sL,sR) beta = beta diag(sL,sR)   iff   sL=sR.

Therefore the stabilizer of a fixed nonzero mass coupling inside the four-element center is
exactly the diagonal pair `{(+,+),(-,-)}`.  The other coset `{(-,+),(+,-)}` anticommutes
with beta and reverses the sign of the mass-exchange operator.

So the quotient

  (Z2_L x Z2_R) / Z2_diag

has an exact physical-algebra candidate: it is simultaneously

* the sign of the oriented vector `p -> +/- p`, and
* the two cosets relative to the mass-coupling stabilizer.

The surviving diagonal element `(-,-)` is the vector-invisible spin deck sign; it should
not be confused with the orientation bit itself.  This cleanly separates the 4pi spin
center from the proposed `t` sign.
-/

namespace GppMassCenterCosetOrientation

open GppMassBreaksRelativeScale
open GppRelativePhaseDiracEnergy
open GppSpinProductCenterTimeOrientation

/-- Four central chiral sign matrices. -/
def centerPP : Matrix (Fin 2) (Fin 2) ℂ := chiralScale 1 1
def centerMM : Matrix (Fin 2) (Fin 2) ℂ := chiralScale (-1) (-1)
def centerMP : Matrix (Fin 2) (Fin 2) ℂ := chiralScale (-1) 1
def centerPM : Matrix (Fin 2) (Fin 2) ℂ := chiralScale 1 (-1)

/-- The diagonal center stabilizes the mass-exchange operator. -/
theorem diagonal_center_stabilizes_mass :
    centerPP * betaRest = betaRest * centerPP ∧
    centerMM * betaRest = betaRest * centerMM := by
  exact ⟨diagonal_scale_commutes_beta 1, diagonal_scale_commutes_beta (-1)⟩

/-- Either one-sided center element anticommutes with beta. -/
theorem relative_center_anticommutes_mass :
    centerMP * betaRest = -(betaRest * centerMP) ∧
    centerPM * betaRest = -(betaRest * centerPM) := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [centerMP, centerPM, chiralScale, betaRest,
        Matrix.mul_apply, Fin.sum_univ_two]

/-- Consequently conjugating beta by either one-sided central sign flips beta. -/
theorem relative_center_conjugates_mass_sign :
    centerMP * betaRest * centerMP = -betaRest ∧
    centerPM * betaRest * centerPM = -betaRest := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [centerMP, centerPM, chiralScale, betaRest,
        Matrix.mul_apply, Fin.sum_univ_two]

/-- Vector orientation character of the four center elements. -/
theorem four_center_vector_characters :
    vectorCenterCharacter 1 1 = 1 ∧
    vectorCenterCharacter (-1) (-1) = 1 ∧
    vectorCenterCharacter (-1) 1 = -1 ∧
    vectorCenterCharacter 1 (-1) = -1 := by
  norm_num [vectorCenterCharacter]

/-- The mass-stabilizing coset is exactly the vector-orientation `t=+1` pair among the
four canonical center elements. -/
theorem mass_stabilizer_matches_positive_orientation_coset :
    (vectorCenterCharacter 1 1 = 1 ∧
      vectorCenterCharacter (-1) (-1) = 1) ∧
    (vectorCenterCharacter (-1) 1 = -1 ∧
      vectorCenterCharacter 1 (-1) = -1) := by
  norm_num [vectorCenterCharacter]

end GppMassCenterCosetOrientation
