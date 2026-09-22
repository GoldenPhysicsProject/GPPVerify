import Mathlib.Tactic
import GppVerify.StandardModel.GaugeSpinCenterRelationalMatter
import GppVerify.CelestialHolography.GooglyTimeOrientationSeparation

/-!
# A fourfold gauge-spin lift of the diagonal charge/orientation transformation

The now-separated ingredients suggest a precise finite candidate lift:

* gauge conjugation:               c -> -c;
* chiral/googly factor exchange:   (sL,sR) -> (sR,sL);
* worldline/vector orientation:    flip one spin-center sign.

Choose the left lift after exchange.  The combined map is

  Xi(c,sL,sR) = (-c,-sR,sL).

It has three striking exact properties:

1. the vector/worldline orientation character `t=sL*sR` flips;
2. therefore the relational gauge-orientation character `m=c*t` is invariant;
3. `Xi^2` is the diagonal spin center `(sL,sR)->(-sL,-sR)`, while charge is restored.
   Hence `Xi^4=id` upstairs, although `Xi^2` is invisible on the vector representation.

This packages the project's recurring `q*t`, factor-exchange, and 4pi/double-cover algebra
into one finite transformation.  It is deliberately named `Xi`, not `CPT`: proving that the
physical QFT CPT operator realizes this exact lift requires the Lorentzian Pin/soldering
and gauge-representation dictionaries.  The theorem is a candidate geometric lift, not an
assertion that standard CPT has order four on physical rays.
-/

namespace GppGaugeSpinCPTLift

open GppGaugeSpinCenterRelationalMatter
open GppSpinProductCenterTimeOrientation

/-- Finite gauge-spin orientation label. -/
structure GSTLabel where
  c : ℝ
  sL : ℝ
  sR : ℝ
  deriving DecidableEq

/-- Combined gauge dualization + factor exchange + one-sided orientation reversal. -/
def Xi (x : GSTLabel) : GSTLabel := ⟨-x.c,-x.sR,x.sL⟩

/-- Relational matter/source character. -/
def XiMatter (x : GSTLabel) : ℝ := matterCharacter3 x.c x.sL x.sR

/-- Vector/worldline orientation character. -/
def XiTime (x : GSTLabel) : ℝ := vectorCenterCharacter x.sL x.sR

/-- One Xi operation reverses the vector/worldline orientation character. -/
theorem Xi_flips_time_orientation (x : GSTLabel) :
    XiTime (Xi x) = - XiTime x := by
  cases x
  simp [XiTime, Xi, vectorCenterCharacter]

/-- Simultaneous gauge reversal compensates that flip, preserving `c*t`. -/
theorem Xi_preserves_matter_character (x : GSTLabel) :
    XiMatter (Xi x) = XiMatter x := by
  cases x
  simp [XiMatter, Xi, matterCharacter3, spinTimeSign, vectorCenterCharacter]

/-- Squaring Xi restores charge and gives precisely the diagonal spin center. -/
theorem Xi_sq_diagonal_center (x : GSTLabel) :
    Xi (Xi x) = ⟨x.c,-x.sL,-x.sR⟩ := by
  cases x
  rfl

/-- The square is invisible to the vector orientation character. -/
theorem Xi_sq_vector_invisible (x : GSTLabel) :
    XiTime (Xi (Xi x)) = XiTime x := by
  rw [Xi_sq_diagonal_center]
  simp [XiTime, vectorCenterCharacter]

/-- Four applications close upstairs. -/
theorem Xi_four (x : GSTLabel) :
    Xi (Xi (Xi (Xi x))) = x := by
  cases x
  rfl

/-- The full finite package. -/
theorem Xi_capstone (x : GSTLabel) :
    XiMatter (Xi x) = XiMatter x ∧
    XiTime (Xi x) = -XiTime x ∧
    Xi (Xi x) = ⟨x.c,-x.sL,-x.sR⟩ ∧
    Xi (Xi (Xi (Xi x))) = x := by
  exact ⟨Xi_preserves_matter_character x,
    Xi_flips_time_orientation x,
    Xi_sq_diagonal_center x,
    Xi_four x⟩

end GppGaugeSpinCPTLift
