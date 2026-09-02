import Mathlib.Tactic
import GppVerify.CelestialHolography.PluckerChiralityAction

/-!
# Split-signature Penrose--Fourier commuting square

In split signature the real Penrose transform may be expressed as an X-ray transform
on real twistor space `RP^3`, while Witten's half-Fourier transform maps a momentum
wavefunction to twistor data.  Performing the complementary half-Fourier transform
instead gives dual-twistor data.  Thus the full twistor-to-dual-twistor Fourier map is
most cleanly viewed as a change of representation through the common momentum model.

This file formalizes the exact categorical consequence of that fact.  The analytic
content (Fourier inversion and the split X-ray/Penrose integral formula) is represented
by explicit inverse/reconstruction hypotheses; no integral theorem is hidden here.

Once the two twistor representations reconstruct the same bulk field, the
correspondence square commutes automatically.  Combining this with the exact real
orientation-reversal theorem for a split Hodge involution relabels a self-dual field as
anti-self-dual (and conversely).  This isolates the remaining mathematical work needed
for a fully analytic theorem: verify the reconstruction hypotheses for the concrete
half-Fourier/X-ray transforms with the desired normalization and function spaces.
-/

namespace GppSplitPenroseFourierSquare

/-- A pair of twistor representations related through a common momentum model. -/
structure CommonMomentumBridge (Mom Tw TwDual Bulk : Type*) where
  toTw : Mom → Tw
  fromTw : Tw → Mom
  toDual : Mom → TwDual
  penrose : Tw → Bulk
  dualPenrose : TwDual → Bulk
  bulkOfMomentum : Mom → Bulk
  twReconstruction : ∀ z, penrose z = bulkOfMomentum (fromTw z)
  dualReconstruction : ∀ m, dualPenrose (toDual m) = bulkOfMomentum m

/-- The induced full twistor-to-dual-twistor transform: inverse half-Fourier to
momentum space, followed by the dual half-Fourier transform. -/
def CommonMomentumBridge.fullFourier
    {Mom Tw TwDual Bulk : Type*}
    (B : CommonMomentumBridge Mom Tw TwDual Bulk) : Tw → TwDual :=
  fun z => B.toDual (B.fromTw z)

/-- The Penrose/Fourier square commutes exactly whenever both twistor representations
reconstruct the same momentum-space bulk field. -/
theorem penrose_fullFourier_commutes
    {Mom Tw TwDual Bulk : Type*}
    (B : CommonMomentumBridge Mom Tw TwDual Bulk)
    (z : Tw) :
    B.dualPenrose (B.fullFourier z) = B.penrose z := by
  rw [CommonMomentumBridge.fullFourier, B.dualReconstruction, B.twReconstruction]

/-- If the ordinary half-Fourier transform is inverted exactly on momentum data, the
full Fourier transform agrees with the dual half-Fourier transform there. -/
theorem fullFourier_on_halfFourier
    {Mom Tw TwDual Bulk : Type*}
    (B : CommonMomentumBridge Mom Tw TwDual Bulk)
    (hinv : ∀ m, B.fromTw (B.toTw m) = m)
    (m : Mom) :
    B.fullFourier (B.toTw m) = B.toDual m := by
  simp [CommonMomentumBridge.fullFourier, hinv]

/-- Consequently both Penrose descriptions of a momentum state give exactly the same
bulk field. -/
theorem two_penrose_representations_same_bulk
    {Mom Tw TwDual Bulk : Type*}
    (B : CommonMomentumBridge Mom Tw TwDual Bulk)
    (hinv : ∀ m, B.fromTw (B.toTw m) = m)
    (m : Mom) :
    B.dualPenrose (B.fullFourier (B.toTw m)) = B.penrose (B.toTw m) := by
  exact B.penrose_fullFourier_commutes (B.toTw m)

/-! ## Adding split-signature chirality

The full Fourier map above is a representation change of the same underlying bulk
solution; by itself it does not alter the physical tensor.  In split signature a real
Hodge operator has eigenvalues `+1` and `-1`.  Reversing orientation replaces `star`
by `-star`, so the very same tensor is relabelled from SD to ASD or conversely.
-/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A bulk field which is self-dual for one orientation is anti-self-dual for the
reversed orientation. -/
theorem same_field_becomes_asd_after_orientation_reversal
    (star : V →ₗ[ℝ] V) (F : V)
    (hF : star F = F) :
    (-star) F = (-1 : ℝ) • F :=
  GppPluckerChiralityAction.orientation_reversal_relabels_sd_as_asd star F hF

/-- Conversely, the same ASD field becomes SD after reversing orientation. -/
theorem same_field_becomes_sd_after_orientation_reversal
    (star : V →ₗ[ℝ] V) (F : V)
    (hF : star F = (-1 : ℝ) • F) :
    (-star) F = F :=
  GppPluckerChiralityAction.orientation_reversal_relabels_asd_as_sd star F hF

/-- Linearized googly reduction in split signature.

Suppose the concrete twistor and dual-twistor transforms reconstruct the same field,
and the source Penrose field is self-dual for the chosen orientation.  Then the
Fourier-related dual-twistor representative reconstructs that same tensor, which is
anti-self-dual for the reversed orientation.  No identification of Fourier with time
reversal or CPT is required. -/
theorem split_linear_googly_from_common_momentum
    {Mom Tw TwDual : Type*}
    (B : CommonMomentumBridge Mom Tw TwDual V)
    (star : V →ₗ[ℝ] V)
    (z : Tw)
    (hSD : star (B.penrose z) = B.penrose z) :
    (-star) (B.dualPenrose (B.fullFourier z)) =
      (-1 : ℝ) • B.dualPenrose (B.fullFourier z) := by
  rw [B.penrose_fullFourier_commutes z]
  exact same_field_becomes_asd_after_orientation_reversal star (B.penrose z) hSD

end GppSplitPenroseFourierSquare
