import Mathlib.Tactic
import GppVerify.CelestialHolography.EinsteinChiralCurvatureBlocks

/-!
# The googly problem as failure of chiral twistor-distribution integrability

For a four-dimensional conformal geometry, the standard twistor distribution on one
projective spin bundle is integrable iff the corresponding chiral Weyl spinor vanishes;
the opposite projective spin bundle has the mirror statement.  Thus a generic spacetime
with both Weyl chiralities present does not possess either ordinary nonlinear-twistor leaf
space globally.

This file records the exact curvature-block logic behind that fact.  We use the two
diagonal Weyl blocks of an Einstein curvature operator as the two Frobenius-obstruction
labels:

    leftIntegrable  <-> W_plus  = 0,
    rightIntegrable <-> W_minus = 0.

The geometric theorem identifying these equalities with Frobenius integrability is standard
external twistor geometry and is not reproved here.  What is proved is the complete algebraic
taxonomy:

* both integrable + Einstein => zero curvature blocks (conformally flat Weyl sector);
* exactly one integrable => a genuinely chiral/self-dual sector;
* neither integrable => the generic two-helicity case;
* orientation/factor exchange swaps the two integrability conditions.

This sharpens the googly target: the generic object should retain both nonintegrable chiral
distributions/contact halves rather than assume that two ordinary twistor leaf spaces exist.
-/

namespace GppGooglyIntegrabilityTaxonomy

open GppEinsteinChiralCurvatureBlocks

variable {K : Type*} [Zero K]

/-- Algebraic proxy for integrability of the first chiral twistor distribution. -/
def LeftTwistorIntegrable (F : CurvatureBlocks K) : Prop := F.pp = 0

/-- Algebraic proxy for integrability of the opposite chiral twistor distribution. -/
def RightTwistorIntegrable (F : CurvatureBlocks K) : Prop := F.mm = 0

/-- Orientation reversal swaps the two twistor-integrability conditions. -/
theorem reversal_swaps_integrability (F : CurvatureBlocks K) :
    LeftTwistorIntegrable (reverseRiemannHodgeOrientation F) ↔
      RightTwistorIntegrable F := by
  rfl

/-- Mirror statement. -/
theorem reversal_swaps_integrability_opposite (F : CurvatureBlocks K) :
    RightTwistorIntegrable (reverseRiemannHodgeOrientation F) ↔
      LeftTwistorIntegrable F := by
  rfl

/-- In the Einstein/block-diagonal sector, simultaneous integrability of both chiral
distributions forces every curvature block in this Weyl/Ricci carrier to vanish. -/
theorem Einstein_and_both_integrable_zero
    (F : CurvatureBlocks K)
    (hEin : MixedBlocksVanish F)
    (hL : LeftTwistorIntegrable F)
    (hR : RightTwistorIntegrable F) :
    F = ⟨0,0,0,0⟩ := by
  rcases F with ⟨pp,pm,mp,mm⟩
  simp [MixedBlocksVanish, LeftTwistorIntegrable, RightTwistorIntegrable] at hEin hL hR ⊢
  aesop

/-- A pure plus Weyl sector has the opposite twistor distribution integrable but the plus
one obstructed whenever its curvature is nonzero. -/
theorem pure_plus_taxonomy (W : K) (hW : W ≠ 0) :
    let F : CurvatureBlocks K := ⟨W,0,0,0⟩
    MixedBlocksVanish F ∧
    (¬ LeftTwistorIntegrable F) ∧
    RightTwistorIntegrable F := by
  simp [MixedBlocksVanish, LeftTwistorIntegrable, RightTwistorIntegrable, hW]

/-- Mirror statement for a pure minus Weyl sector. -/
theorem pure_minus_taxonomy (W : K) (hW : W ≠ 0) :
    let F : CurvatureBlocks K := ⟨0,0,0,W⟩
    MixedBlocksVanish F ∧
    LeftTwistorIntegrable F ∧
    (¬ RightTwistorIntegrable F) := by
  simp [MixedBlocksVanish, LeftTwistorIntegrable, RightTwistorIntegrable, hW]

/-- Generic Einstein two-helicity curvature has neither chiral twistor distribution
integrable when both Weyl blocks are nonzero. -/
theorem generic_Einstein_neither_integrable
    (Wplus Wminus : K) (hp : Wplus ≠ 0) (hm : Wminus ≠ 0) :
    let F : CurvatureBlocks K := ⟨Wplus,0,0,Wminus⟩
    MixedBlocksVanish F ∧
    (¬ LeftTwistorIntegrable F) ∧
    (¬ RightTwistorIntegrable F) := by
  simp [MixedBlocksVanish, LeftTwistorIntegrable, RightTwistorIntegrable, hp, hm]

/-- Yet orientation reversal of the generic two-helicity case simply exchanges the two
existing obstructions; it does not create a missing curvature sector. -/
theorem generic_reversal_exchanges_obstructions
    (Wplus Wminus : K) :
    reverseRiemannHodgeOrientation (⟨Wplus,0,0,Wminus⟩ : CurvatureBlocks K) =
      ⟨Wminus,0,0,Wplus⟩ := by
  rfl

end GppGooglyIntegrabilityTaxonomy
