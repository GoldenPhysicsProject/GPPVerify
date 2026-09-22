import Mathlib.Tactic
import GppVerify.StandardModel.GaugeSpinCPTLift
import GppVerify.CelestialHolography.WeylQuarticNullReconstruction

/-!
# Finite capstone: one lift can carry gauge reversal, time orientation, and googly exchange

The previous modules isolate two exact structures:

* `Xi(c,sL,sR)=(-c,-sR,sL)`, which preserves the relational `c*t` character, reverses
  the oriented-vector sign `t=sL*sR`, and squares to the diagonal spin center;
* the paired chiral Weyl carrier `(W_left,W_right)`, on which googly/factor exchange simply
  swaps the two binary quartics.

Because a one-sided spin-center sign is invisible to rank-four Weyl spinors, the natural
induced gravity action of the spin part of `Xi` is just the factor exchange

  (W_left,W_right) -> (W_right,W_left).

This module packages those actions into one finite transformation.  After one application:

  charge sign flips,
  vector/worldline orientation flips,
  matter character c*t is unchanged,
  the two Weyl chiralities are exchanged.

After two applications the Weyl pair is restored and only the diagonal spin deck sign
remains upstairs.  Four applications close exactly.

This is NOT yet the nonlinear googly theorem: the hard missing step is to prove that the
actual curved contact/Jacobi reconstruction produces the paired Weyl quartics and that its
factor exchange intertwines with this finite action.  The present result fixes the target
symmetry algebra that such a reconstruction should realize.
-/

namespace GppGooglyGaugeSpinLiftCapstone

open GppGaugeSpinCPTLift
open GppWeylQuarticNullReconstruction

/-- Combined finite label carrying gauge/spin orientation and both Weyl chiralities. -/
structure FullLiftLabel where
  gst : GSTLabel
  weyl : WeylPair
  deriving DecidableEq

/-- Candidate combined lift. -/
def fullXi (x : FullLiftLabel) : FullLiftLabel :=
  ⟨Xi x.gst, exchangeWeyl x.weyl⟩

/-- One lift preserves the relational matter character. -/
theorem fullXi_preserves_matter (x : FullLiftLabel) :
    XiMatter (fullXi x).gst = XiMatter x.gst := by
  exact Xi_preserves_matter_character x.gst

/-- One lift reverses the vector/worldline orientation character. -/
theorem fullXi_flips_time (x : FullLiftLabel) :
    XiTime (fullXi x).gst = -XiTime x.gst := by
  exact Xi_flips_time_orientation x.gst

/-- One lift exchanges the two chiral Weyl quartics. -/
theorem fullXi_swaps_weyl (x : FullLiftLabel) :
    (fullXi x).weyl.left = x.weyl.right ∧
    (fullXi x).weyl.right = x.weyl.left := by
  rfl

/-- Two lifts restore the Weyl pair and leave only the diagonal spin-center sign upstairs. -/
theorem fullXi_sq (x : FullLiftLabel) :
    fullXi (fullXi x) =
      ⟨⟨x.gst.c,-x.gst.sL,-x.gst.sR⟩,x.weyl⟩ := by
  cases x with
  | mk gst W =>
    cases gst with
    | mk c sL sR =>
      cases W with
      | mk WL WR =>
        rfl

/-- Four lifts close on the complete finite carrier. -/
theorem fullXi_four (x : FullLiftLabel) :
    fullXi (fullXi (fullXi (fullXi x))) = x := by
  cases x with
  | mk gst W =>
    cases gst with
    | mk c sL sR =>
      cases W with
      | mk WL WR =>
        rfl

/-- The complete symmetry package. -/
theorem fullXi_capstone (x : FullLiftLabel) :
    XiMatter (fullXi x).gst = XiMatter x.gst ∧
    XiTime (fullXi x).gst = -XiTime x.gst ∧
    (fullXi x).weyl.left = x.weyl.right ∧
    (fullXi x).weyl.right = x.weyl.left ∧
    fullXi (fullXi (fullXi (fullXi x))) = x := by
  exact ⟨fullXi_preserves_matter x,
    fullXi_flips_time x,
    (fullXi_swaps_weyl x).1,
    (fullXi_swaps_weyl x).2,
    fullXi_four x⟩

end GppGooglyGaugeSpinLiftCapstone
