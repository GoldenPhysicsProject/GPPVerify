import Mathlib.Tactic
import GppVerify.CelestialHolography.WeylQuarticNullReconstruction
import GppVerify.CelestialHolography.EinsteinChiralCurvatureBlocks

/-!
# Vacuum Einstein curvature from the two chiral null-direction quartics

In four dimensions an Einstein curvature operator is block diagonal with respect to the
Hodge/chiral splitting.  In vacuum (zero scalar curvature for the present schematic
carrier) its two nonzero blocks are exactly the two Weyl spinors.

Each symmetric rank-four Weyl spinor is equivalently a binary quartic on its projective
spin line.  `WeylQuarticNullReconstruction` proves that five explicit affine samples
determine one quartic, hence ten samples determine the pair.

This module combines those facts at the finite algebraic level: a paired Weyl quartic maps
injectively to the diagonal Einstein-curvature carrier, and exchanging the two quartics is
EXACTLY the same block operation as reversing the Hodge orientation.

Thus, once a curved null/contact construction produces the two quartic functions, the
remaining algebraic googly reconstruction is unique.  The unsolved geometric step is now
sharply isolated: derive those quartics from the actual Jacobi/contact/Frobenius obstruction
of the nonchiral null-ray geometry.
-/

namespace GppEinsteinWeylQuarticReconstruction

open GppWeylQuarticNullReconstruction
open GppEinsteinChiralCurvatureBlocks

/-- Vacuum Einstein curvature carrier built from the two Weyl quartics. -/
def vacuumCurvature (W : WeylPair) : CurvatureBlocks Quartic5 :=
  ⟨W.left, ⟨0,0,0,0,0⟩, ⟨0,0,0,0,0⟩, W.right⟩

/-- It is mixed-block-free by construction. -/
theorem vacuumCurvature_is_Einstein_pattern (W : WeylPair) :
    MixedBlocksVanish (vacuumCurvature W) := by
  simp [MixedBlocksVanish, vacuumCurvature]

/-- The map from paired Weyl quartics to vacuum curvature is injective. -/
theorem vacuumCurvature_injective : Function.Injective vacuumCurvature := by
  intro W V h
  cases W with
  | mk WL WR =>
    cases V with
    | mk VL VR =>
      have hL := congrArg (fun F : CurvatureBlocks Quartic5 => F.pp) h
      have hR := congrArg (fun F : CurvatureBlocks Quartic5 => F.mm) h
      simp [vacuumCurvature] at hL hR
      cases hL
      cases hR
      rfl

/-- Googly/factor exchange of the two Weyl quartics intertwines exactly with Hodge-
orientation reversal of the Einstein curvature blocks. -/
theorem exchangeWeyl_intertwines_Hodge_orientation (W : WeylPair) :
    vacuumCurvature (exchangeWeyl W) =
      reverseRiemannHodgeOrientation (vacuumCurvature W) := by
  cases W
  rfl

/-- Applying the exchange twice restores the curvature. -/
theorem googly_exchange_curvature_involution (W : WeylPair) :
    vacuumCurvature (exchangeWeyl (exchangeWeyl W)) = vacuumCurvature W := by
  rw [exchangeWeyl_involution]

/-- Ten null-direction samples determine the full vacuum curvature carrier. -/
theorem vacuumCurvature_ext_ten_samples
    (W V : WeylPair)
    (l0 : qeval W.left 0 = qeval V.left 0)
    (l1 : qeval W.left 1 = qeval V.left 1)
    (lm1 : qeval W.left (-1) = qeval V.left (-1))
    (l2 : qeval W.left 2 = qeval V.left 2)
    (lm2 : qeval W.left (-2) = qeval V.left (-2))
    (r0 : qeval W.right 0 = qeval V.right 0)
    (r1 : qeval W.right 1 = qeval V.right 1)
    (rm1 : qeval W.right (-1) = qeval V.right (-1))
    (r2 : qeval W.right 2 = qeval V.right 2)
    (rm2 : qeval W.right (-2) = qeval V.right (-2)) :
    vacuumCurvature W = vacuumCurvature V := by
  have hWV := weylPair_ext_ten_samples W V l0 l1 lm1 l2 lm2 r0 r1 rm1 r2 rm2
  rw [hWV]

/-- The two algebraic arrows of the local googly square now commute exactly. -/
theorem local_googly_reconstruction_square (W : WeylPair) :
    MixedBlocksVanish (vacuumCurvature W) ∧
    MixedBlocksVanish (vacuumCurvature (exchangeWeyl W)) ∧
    vacuumCurvature (exchangeWeyl W) =
      reverseRiemannHodgeOrientation (vacuumCurvature W) := by
  exact ⟨vacuumCurvature_is_Einstein_pattern W,
    vacuumCurvature_is_Einstein_pattern (exchangeWeyl W),
    exchangeWeyl_intertwines_Hodge_orientation W⟩

end GppEinsteinWeylQuarticReconstruction
