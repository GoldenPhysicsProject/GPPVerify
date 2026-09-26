import Mathlib.Tactic
import GppVerify.CelestialHolography.TaggedAmbitwistorParity
import GppVerify.CelestialHolography.EinsteinChiralCurvatureBlocks

/-!
# Tagged ambitwistor criterion for the full Einstein googly exchange

The nonchiral candidate parent is ambitwistor space: a twistor and a dual twistor subject
to incidence.  `TaggedAmbitwistorParity` keeps these two representation types distinct and
proves that exchanging the two projections is involutive.  Independently,
`EinsteinChiralCurvatureBlocks` proves that reversing four-orientation exchanges the two
Hodge-diagonal Weyl sectors while preserving the Einstein/mixed-block-free pattern.

The one genuinely geometric bridge still needed between those statements is:

    curvature(exchange a) = HodgeOrientationReverse(curvature(a)).

This file isolates that equation as the *single* input of a tagged ambitwistor-to-curvature
reconstruction.  Once it is supplied, all of the desired googly consequences follow:

* the two chiral curvature sectors are exchanged rather than one being manufactured from
  the other;
* the Einstein block condition is invariant;
* a pure plus-helicity configuration is carried to the corresponding pure minus-helicity
  configuration;
* exchanging twice restores the original curvature data.

No claim is made here that the input equation has already been proved for a general curved
ambitwistor space.  Classical LeBrun/Baston--Mason results reconstruct conformal geometry
from spaces of complex null geodesics and characterize conformally Einstein metrics by
appropriate formal-neighbourhood/thickening data under stated hypotheses; connecting the
specific tagged factor exchange used here to Hodge-orientation reversal of that reconstructed
curvature is the precise GPP bridge to prove.
-/

namespace GppTaggedAmbitwistorEinsteinGooglyCriterion

open GppTaggedAmbitwistorParity
open GppEinsteinChiralCurvatureBlocks

variable {K : Type*} [Zero K]

/-- A curvature reconstruction attached to the two tagged ambitwistor orientations.
The only nontrivial compatibility field is the googly intertwining equation. -/
structure CurvatureBridge where
  curvature : Ambitwistor → CurvatureBlocks K
  oppositeCurvature : OppositeAmbitwistor → CurvatureBlocks K
  exchange_intertwines : ∀ a,
    oppositeCurvature (exchange a) =
      reverseRiemannHodgeOrientation (curvature a)

namespace CurvatureBridge

variable (B : CurvatureBridge (K:=K))

/-- The reverse tagged exchange automatically has the converse curvature intertwining law;
no second compatibility hypothesis is needed. -/
theorem exchangeBack_intertwines (b : OppositeAmbitwistor) :
    B.curvature (exchangeBack b) =
      reverseRiemannHodgeOrientation (B.oppositeCurvature b) := by
  have h := B.exchange_intertwines (exchangeBack b)
  rw [exchange_exchangeBack] at h
  have hr := congrArg reverseRiemannHodgeOrientation h
  simpa [reverseRiemannHodgeOrientation_involution] using hr.symm

/-- The plus Hodge block after tagged exchange is exactly the original minus block. -/
theorem exchanged_plus_eq_original_minus (a : Ambitwistor) :
    (B.oppositeCurvature (exchange a)).pp = (B.curvature a).mm := by
  rw [B.exchange_intertwines]
  rfl

/-- Likewise the exchanged minus block is exactly the original plus block. -/
theorem exchanged_minus_eq_original_plus (a : Ambitwistor) :
    (B.oppositeCurvature (exchange a)).mm = (B.curvature a).pp := by
  rw [B.exchange_intertwines]
  rfl

/-- The Einstein/mixed-block-free condition is invariant under the googly exchange. -/
theorem exchanged_einstein_iff_original (a : Ambitwistor) :
    MixedBlocksVanish (B.oppositeCurvature (exchange a)) ↔
      MixedBlocksVanish (B.curvature a) := by
  rw [B.exchange_intertwines]
  exact mixedBlocksVanish_reverseRiemannHodgeOrientation (B.curvature a)

/-- Conversely the Einstein condition is invariant when starting from the opposite tagging. -/
theorem exchangeBack_einstein_iff_original (b : OppositeAmbitwistor) :
    MixedBlocksVanish (B.curvature (exchangeBack b)) ↔
      MixedBlocksVanish (B.oppositeCurvature b) := by
  rw [B.exchangeBack_intertwines]
  exact mixedBlocksVanish_reverseRiemannHodgeOrientation (B.oppositeCurvature b)

/-- A pure plus-diagonal curvature configuration is sent to the corresponding pure
minus-diagonal configuration. -/
theorem pure_plus_exchanges_to_pure_minus
    (a : Ambitwistor) (Fplus : K)
    (h : B.curvature a = ⟨Fplus,0,0,0⟩) :
    B.oppositeCurvature (exchange a) = ⟨0,0,0,Fplus⟩ := by
  rw [B.exchange_intertwines, h]
  rfl

/-- And a pure minus configuration is sent to pure plus. -/
theorem pure_minus_exchanges_to_pure_plus
    (a : Ambitwistor) (Fminus : K)
    (h : B.curvature a = ⟨0,0,0,Fminus⟩) :
    B.oppositeCurvature (exchange a) = ⟨Fminus,0,0,0⟩ := by
  rw [B.exchange_intertwines, h]
  rfl

/-- Round-trip exchange restores the original reconstructed curvature exactly. -/
theorem curvature_round_trip (a : Ambitwistor) :
    B.curvature (exchangeBack (exchange a)) = B.curvature a := by
  rw [exchangeBack_exchange]

end CurvatureBridge

end GppTaggedAmbitwistorEinsteinGooglyCriterion
