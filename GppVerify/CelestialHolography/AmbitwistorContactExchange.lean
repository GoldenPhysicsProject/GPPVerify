import Mathlib.Tactic
import GppVerify.CelestialHolography.TaggedAmbitwistorParity
import GppVerify.CelestialHolography.KleinCliffordPinConjugation
import GppVerify.CelestialHolography.KleinWeylReflectionConjugacy
import GppVerify.CelestialHolography.FlatNullWeylFiberGeometry
import GppVerify.CelestialHolography.NullConeEinsteinSelector
import GppVerify.CelestialHolography.EinsteinNullRaySL2Geometry

/-!
# Ambitwistor factor exchange is anti-contact at the flat incidence level

The flat four-dimensional ambitwistor model is the incidence quadric `Z.W=0` in a
twistor/dual-twistor product.  Its standard symplectic potential is proportional to

  Theta = Z.dW - W.dZ.

Exchanging the two chiral factors therefore reverses the sign of `Theta`.  On the
projectivized incidence space this preserves the contact hyperplane distribution while
reversing the chosen contact one-form/coorientation.

The imported companion modules now place this anti-contact statement inside the sharper
finite-dimensional spine:

* `KleinCliffordPinConjugation` proves the polarized Clifford relation and the internal
  Pin-adjoint implementation of non-null Klein reflection;
* `KleinWeylReflectionConjugacy` identifies the positive-norm cosmological reflection as
  a split-dilation conjugate of one fixed Weyl reflection;
* `FlatNullWeylFiberGeometry` records the projective `RP^1` kernel/unipotent geometry left
  when the pointwise reflection becomes singular at flat infinity;
* `NullConeEinsteinSelector` proves that a quadratic tensor vanishing on every split null
  direction is necessarily pure trace, the algebraic converse behind the null-geodesic
  form of the almost-Einstein equation;
* `EinsteinNullRaySL2Geometry` proves that the associated rank-two null-ray state geometry
  is symplectic/`SL(2)` at the finite-dimensional level and contains the same Weyl and
  unipotent matrices used by the flat celestial kernel.

The analytic Knapp--Stein/light-transform integral, the curved correspondence-space
realization of the Einstein bundle, and a general curved orientation-reversal theorem
remain external/open.  None of those claims is hidden in the imports here.

This module formalizes the underlying bilinear algebra with the twistor and dual-twistor
tags kept distinct.  It does not formalize differential forms, projectivization, or claim
that every curved ambitwistor space has a global factor-exchange symmetry.
-/

namespace GppAmbitwistorContactExchange

open GppTwistorAnnihilatorIncidence
open GppTaggedAmbitwistorParity

/-- Linearized incidence condition tangent to `Z.W=0`:
`dZ.W + Z.dW = 0`. -/
def TangentIncidence
    (z : Twistor) (w : DualTwistor)
    (dz : Twistor) (dw : DualTwistor) : Prop :=
  pair4 dz.val w.val + pair4 z.val dw.val = 0

/-- One representative of the contact/symplectic potential, `W.dZ`. -/
def thetaLeft (w : DualTwistor) (dz : Twistor) : ℝ :=
  pair4 dz.val w.val

/-- The exchanged representative, `Z.dW`. -/
def thetaRight (z : Twistor) (dw : DualTwistor) : ℝ :=
  pair4 z.val dw.val

/-- On tangent vectors to the incidence quadric, the two one-sided contact
representatives differ by a sign. -/
theorem thetaRight_eq_neg_thetaLeft_on_incidence
    (z : Twistor) (w : DualTwistor)
    (dz : Twistor) (dw : DualTwistor)
    (h : TangentIncidence z w dz dw) :
    thetaRight z dw = - thetaLeft w dz := by
  dsimp [TangentIncidence, thetaLeft, thetaRight] at h ⊢
  linarith

/-- Therefore their kernels agree: factor exchange preserves the contact hyperplane. -/
theorem contact_kernel_preserved_on_incidence
    (z : Twistor) (w : DualTwistor)
    (dz : Twistor) (dw : DualTwistor)
    (h : TangentIncidence z w dz dw) :
    thetaLeft w dz = 0 ↔ thetaRight z dw = 0 := by
  rw [thetaRight_eq_neg_thetaLeft_on_incidence z w dz dw h]
  constructor <;> intro hz
  · simp [hz]
  · simpa using neg_eq_zero.mp hz

/-- Symmetric flat ambitwistor potential (irrelevant overall constants suppressed). -/
def ambiPotential
    (z : Twistor) (w : DualTwistor)
    (dz : Twistor) (dw : DualTwistor) : ℝ :=
  thetaRight z dw - thetaLeft w dz

/-- The same potential after exchanging the tagged twistor and dual-twistor slots. -/
def exchangedPotential
    (w : DualTwistor) (z : Twistor)
    (dw : DualTwistor) (dz : Twistor) : ℝ :=
  thetaLeft w dz - thetaRight z dw

/-- Chiral factor exchange reverses the flat ambitwistor symplectic/contact potential. -/
theorem factor_exchange_negates_potential
    (z : Twistor) (w : DualTwistor)
    (dz : Twistor) (dw : DualTwistor) :
    exchangedPotential w z dw dz = - ambiPotential z w dz dw := by
  simp [exchangedPotential, ambiPotential, thetaLeft, thetaRight]
  ring

/-- The anti-contact sign is itself involutive: exchanging twice restores the potential. -/
theorem factor_exchange_twice_restores_potential
    (z : Twistor) (w : DualTwistor)
    (dz : Twistor) (dw : DualTwistor) :
    - exchangedPotential w z dw dz = ambiPotential z w dz dw := by
  rw [factor_exchange_negates_potential]
  ring

end GppAmbitwistorContactExchange
