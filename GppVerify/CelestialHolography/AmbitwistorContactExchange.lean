import Mathlib.Tactic
import GppVerify.CelestialHolography.TaggedAmbitwistorParity
import GppVerify.CelestialHolography.AmbitwistorSecondOrderIncidence
import GppVerify.CelestialHolography.AmbitwistorContactNeutralCone
import GppVerify.CelestialHolography.KleinCliffordPinConjugation
import GppVerify.CelestialHolography.KleinWeylReflectionConjugacy
import GppVerify.CelestialHolography.FlatNullWeylFiberGeometry
import GppVerify.CelestialHolography.InfinityLeviScreenGeometry
import GppVerify.CelestialHolography.ConformalInfinityConeFactorization
import GppVerify.CelestialHolography.NullConeEinsteinSelector
import GppVerify.CelestialHolography.EinsteinNullRaySL2Geometry
import GppVerify.CelestialHolography.EinsteinScaleProjectiveFiber
import GppVerify.CelestialHolography.SkyEinsteinIntrinsicSpine
import GppVerify.CelestialHolography.NullOpticalRicciWeylSplit
import GppVerify.CelestialHolography.NullSurfaceEinsteinBundleBridge
import GppVerify.CelestialHolography.NSFSkyAffineParameterBridge
import GppVerify.CelestialHolography.EinsteinChiralCurvatureBlocks
import GppVerify.CelestialHolography.NSFOppositeHelicityTailCoupling

/-!
# Ambitwistor contact exchange, second-order incidence, and the neutral contact screen

The flat four-dimensional ambitwistor model is the incidence quadric `Z.W=0` in a
twistor/dual-twistor product.  Its standard symplectic potential is proportional to

  Theta = Z.dW - W.dZ.

Exchanging the two chiral factors therefore reverses the sign of `Theta`.  On the
projectivized incidence space this preserves the contact hyperplane distribution while
reversing the chosen contact one-form/coorientation.

The imported companion modules now place this anti-contact statement inside a broader,
carefully separated spine:

* the Klein/Clifford modules give the metric-free incidence geometry, the non-null Pin
  reflection, and the flat null degeneration;
* the infinity-screen modules derive the split celestial screen and its two spinor factors;
* `AmbitwistorSecondOrderIncidence` formalizes Penrose's TN41 observation that the two
  chiral weak-incidence conditions coincide to first order on the ambitwistor tangent
  hyperplane, while exact strong incidence along an affine displacement is controlled by
  the quadratic term `dZ.dW`;
* `AmbitwistorContactNeutralCone` formalizes the universal rank-two Lagrangian-contact
  algebra: for a contact splitting `H=L_-+L_+`, the Levi pairing plus para-complex splitting
  gives a neutral quadratic form `q(X,Y)=2 Y^T X`, so the standard contact-null condition
  is exactly `Y^T X=0`.  Standard type-A Lagrangian-contact geometry supplies the external
  identification of these halves with the two projective ambitwistor projections;
* the sky modules refine the intrinsic real datum from bare contact space to the light-ray
  space together with its distinguished family of skies, and identify the exact finite
  null-cone algebra behind the Einstein selector;
* `NullOpticalRicciWeylSplit` separates the two-dimensional optical/Jacobi curvature into
  its scalar trace and trace-free part.  Under the standard geometric interpretation the
  former is null Ricci focusing and the latter is the projected Weyl/shear information,
  making explicit that solving the Einstein-scale trace problem does not erase the graviton;
* `NullSurfaceEinsteinBundleBridge` proves the scalar coefficient equivalence between the
  NSF second-order conformal-scale equation and the null almost-Einstein equation once the
  curvature-sign convention is made explicit;
* `NSFSkyAffineParameterBridge` records the reciprocal-rate algebra showing that the NSF
  physical affine parameter and the normalized projective solution ratio have the same
  derivative along a ray;
* `EinsteinChiralCurvatureBlocks` records the block-diagonal Einstein pattern and the fact
  that reversing Hodge orientation exchanges already existing chiral blocks rather than
  generating one from the other;
* `NSFOppositeHelicityTailCoupling` formalizes the narrowly scoped 2026 NSF selection rule
  for the quadratic cone-source two-annihilation/tail sector: equal-helicity coefficients
  vanish there, so a nonzero selected tail source requires both helicity sectors.  It does
  NOT claim that every nonlinear graviton process has this selection rule; equal-helicity
  four-graviton channels can be nonzero.

Penrose's TN41 second-order strong-incidence condition and the standard contact-null cone
now agree at the level of the homogeneous Lagrangian-contact model.  What is not yet
formalized is the full chart theorem carrying a general projective ambitwistor tangent
vector `(dZ,dW)` to the rank-two contact-half coordinates `(X,Y)` globally/projectively.
Nor is it yet proved that the curvature of the evolving sky Jacobi plane is exactly the
curved deformation of Penrose's second-order strong-incidence cone.  Those are the next
geometric bridge theorems rather than assumptions hidden in this file.

The analytic Knapp--Stein/light-transform integrals, NSF metricity/descent as a differential
system, the global holomorphic identification `E_sky = E_NSF = E_LeBrun`, and a general
curved factor-exchange symmetry remain external/open.  None of those claims is hidden in
the imports here.

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
