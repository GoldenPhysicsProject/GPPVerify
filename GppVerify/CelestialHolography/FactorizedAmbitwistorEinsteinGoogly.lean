import Mathlib.Tactic
import GppVerify.CelestialHolography.TaggedAmbitwistorParity
import GppVerify.CelestialHolography.EinsteinChiralCurvatureBlocks
import GppVerify.CelestialHolography.TaggedAmbitwistorEinsteinGooglyCriterion

/-!
# Factorized ambitwistor reconstruction makes the Einstein googly exchange automatic

The previous `TaggedAmbitwistorEinsteinGooglyCriterion` isolated the desired curved bridge
as an equation

    curvature(exchange a) = HodgeReverse(curvature(a)).

This file sharpens the target.  In four-dimensional Einstein geometry the curvature
operator on two-forms is block diagonal with two chiral Weyl blocks.  Suppose those two
blocks are reconstructed separately from the two tagged ambitwistor projections:

    W_plus  = plusCurvature(Z),
    W_minus = minusCurvature(W).

Then there is no additional googly equation to assume.  The Einstein curvature attached to
`(Z,W)` is

    [[W_plus,0],[0,W_minus]],

while the curvature attached to the exchanged tagged pair `(W,Z)` is

    [[W_minus,0],[0,W_plus]].

That is *definitionally* the Hodge-orientation reversal of the original block matrix.
Thus the remaining geometric problem is reduced to the chiral factorization theorem:
prove that the full Einstein/ambitwistor reconstruction really recovers the two diagonal
Weyl blocks from the two projections separately.  Once that is established, factor
exchange solves the SD/ASD bookkeeping automatically.

This is an exact algebraic theorem.  It does not assert the analytic Penrose/LeBrun/Baston-
Mason reconstruction or its factorization; those are the remaining geometric inputs.
-/

namespace GppFactorizedAmbitwistorEinsteinGoogly

open GppTaggedAmbitwistorParity
open GppEinsteinChiralCurvatureBlocks

variable {K : Type*} [Zero K]

/-- Separate reconstruction maps for the two chiral ambitwistor projections. -/
structure ChiralReconstruction where
  plusCurvature : Twistor → K
  minusCurvature : DualTwistor → K

namespace ChiralReconstruction

variable (R : ChiralReconstruction (K:=K))

/-- Einstein curvature reconstructed from an ordinarily tagged ambitwistor pair. -/
def curvature (a : Ambitwistor) : CurvatureBlocks K :=
  ⟨R.plusCurvature a.z, 0, 0, R.minusCurvature a.w⟩

/-- The same reconstruction on the opposite tagging.  The representation types remain
separate: the dual-twistor projection supplies the plus slot of the reversed orientation,
while the ordinary-twistor projection supplies its minus slot. -/
def oppositeCurvature (a : OppositeAmbitwistor) : CurvatureBlocks K :=
  ⟨R.minusCurvature a.w, 0, 0, R.plusCurvature a.z⟩

/-- Main theorem: once Einstein curvature factorizes through the two chiral projections,
tagged ambitwistor exchange is exactly Hodge-orientation reversal.  No independent googly
compatibility axiom remains. -/
theorem exchange_is_hodgeOrientationReverse (a : Ambitwistor) :
    R.oppositeCurvature (exchange a) =
      reverseRiemannHodgeOrientation (R.curvature a) := by
  rfl

/-- Both original and exchanged reconstructions are automatically Einstein/block diagonal. -/
theorem both_reconstructions_mixedBlocksVanish (a : Ambitwistor) :
    MixedBlocksVanish (R.curvature a) ∧
    MixedBlocksVanish (R.oppositeCurvature (exchange a)) := by
  simp [curvature, oppositeCurvature, MixedBlocksVanish]

/-- The exchanged plus block is the original minus Weyl block. -/
theorem exchanged_plus_eq_original_minus (a : Ambitwistor) :
    (R.oppositeCurvature (exchange a)).pp = (R.curvature a).mm := by
  rfl

/-- The exchanged minus block is the original plus Weyl block. -/
theorem exchanged_minus_eq_original_plus (a : Ambitwistor) :
    (R.oppositeCurvature (exchange a)).mm = (R.curvature a).pp := by
  rfl

/-- Round-trip tagged exchange restores the same factorized Einstein curvature. -/
theorem roundTrip_curvature (a : Ambitwistor) :
    R.curvature (exchangeBack (exchange a)) = R.curvature a := by
  rw [exchangeBack_exchange]

/-- The factorized construction canonically supplies the abstract compatibility structure
used by the earlier criterion module. -/
def toCurvatureBridge :
    GppTaggedAmbitwistorEinsteinGooglyCriterion.CurvatureBridge (K:=K) where
  curvature := R.curvature
  oppositeCurvature := R.oppositeCurvature
  exchange_intertwines := R.exchange_is_hodgeOrientationReverse

end ChiralReconstruction

end GppFactorizedAmbitwistorEinsteinGoogly
