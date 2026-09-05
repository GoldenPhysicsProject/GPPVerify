import Mathlib.Tactic
import GppVerify.CelestialHolography.FourierEpsilonCliffordSupport
import GppVerify.CelestialHolography.FlatInfinityChiralComplex
import GppVerify.CelestialHolography.FlatInfinityCelestialFactorization
import GppVerify.CelestialHolography.CelestialLightWeylIntertwiners
import GppVerify.CelestialHolography.FourierLightShadowDiamond
import GppVerify.CelestialHolography.PrincipalSeriesLightPlancherelMatch
import GppVerify.CelestialHolography.EinsteinInfinityTwistorFamily
import GppVerify.CelestialHolography.KleinPinReflectionDegeneration
import GppVerify.CelestialHolography.AmbitwistorContactExchange
import GppVerify.CelestialHolography.OrientationProjectorSwap
import GppVerify.CelestialHolography.SpinorEinsteinCorrespondenceSelector
import GppVerify.CelestialHolography.FourierDualSplitPolarity
import GppVerify.CelestialHolography.KleinSpinorIncidence
import GppVerify.CelestialHolography.SplitGooglyGeometryCapstone
import GppVerify.CelestialHolography.TwistorCanonicalShift
import GppVerify.CelestialHolography.TwistorRepresentationConvention

/-!
# Googly geometry intertwiner spine

This file packages the strongest exact finite-dimensional part of the GPP googly
construction currently available.

The canonical core no longer requires a pointwise identification `V* ≅ V`.  Starting
from a spacetime/Klein point `p` and the Fourier phase restricted to its twistor 2-plane,
one has the exact metric-free chain

  Fourier support
    = annihilator incidence in V*
    = epsilon middle-degree dual Plucker plane
    = kernel of the chiral Clifford map cMinus(p) : V* -> V.

The same Klein bivector acts on the two half-spinor modules `V` and `V*` by

  cPlus(p)  : V  -> V*,
  cMinus(p) : V* -> V,

and their compositions are `-Q_Klein(p)` times the identity.  On the Klein quadric
`Q_Klein(p)=0`, the action is therefore nilpotent and its two kernels are exactly the
twistor line and its dual annihilator line.  This is intrinsic incidence geometry, not
a hidden metric polarity.

`EinsteinInfinityTwistorFamily` packages the one-parameter family
`I_Lambda=(Lambda,0,0,0,0,1)`.  Its Klein norm is `Lambda`, so for nonzero `Lambda`
the two chiral Clifford maps are inverse up to the scalar `-Lambda`; at `Lambda=0` the
bridge degenerates to the flat null complex below.  The identification of this algebraic
family with the curved parallel scale tractor/infinity twistor is an external geometric
input, not a theorem of this file.

`KleinPinReflectionDegeneration` supplies the corresponding vector-side operation for
`Lambda != 0`: reflection in the non-null Klein vector `I_Lambda` preserves `Q_Klein`,
is involutive, and has active `(p01,p23)` block determinant `-1`.
`KleinCliffordPinConjugation`, imported transitively through `AmbitwistorContactExchange`,
adds the coordinate Clifford anticommutator and the adjoint identity which implements
that same Klein reflection on Clifford multiplication.  Thus the finite coordinate Pin
bridge is now stated internally rather than merely inferred from the abstract Pin-group
theorem.  This Pin/Klein reflection is a discrete conformal-representation operation; it
must not be conflated with mere reversal of the four-dimensional orientation label.

At the standard flat infinity point the two chiral maps form an exact two-periodic
complex.  The two two-dimensional kernel factors give the split celestial spinors and
the rank-one null-momentum factorization formalized in
`FlatInfinityCelestialFactorization`.

At the representation-label level, `CelestialLightWeylIntertwiners` keeps three distinct
operations separate:

* left light reflection `L : (h,hbar) -> (1-h,hbar)`;
* right light reflection `Lbar : (h,hbar) -> (h,1-hbar)`;
* chiral factor exchange `P : (h,hbar) -> (hbar,h)`.

Their product `L Lbar` is full shadow, while `P L P = Lbar`; parity/factor exchange is
therefore not identified with shadow.  `FourierLightShadowDiamond` packages the exact
logical consequence of the two externally established half-Fourier/light commuting
squares: their composition intertwines full Fourier with `Lbar L`, hence with shadow at
the weight level.  No analytic integral is hidden in that module; the two commuting
squares are explicit assumptions.  `PrincipalSeriesLightPlancherelMatch` records the
closed-form normalization relation to the odd real principal-series density.

`AmbitwistorContactExchange` gives an independent FLAT-incidence statement.  On
`Z.W=0`, exchanging the two tagged twistor/dual-twistor projections reverses the standard
ambitwistor potential while preserving its kernel/contact hyperplane.  This is an exact
anti-contact factor-exchange theorem in the flat coordinate model.

Crucial distinction: standard light-ray/contact geometry is determined by the conformal
class and does not require a choice of four-dimensional spacetime orientation.  Therefore
four-orientation reversal does not move the underlying unparametrized null geodesic in
intrinsic ambitwistor/light-ray space.  Its bulk action is instead the Hodge relabelling
`star -> -star`.  `OrientationProjectorSwap` proves for a completely generic complexified
curvature/two-form field that

  P_plus[-o](F)  = P_minus[o](F),
  P_minus[-o](F) = P_plus[o](F),

while the underlying field `F` is unchanged.  Thus flat anti-contact factor exchange and
spacetime orientation reversal are distinct operations and are no longer identified here.

The transitive Einstein-selector modules record a second major bridge.  Vanishing of the
almost-Einstein quadratic tensor on all split null directions forces it to be pure trace.
`SpinorEinsteinCorrespondenceSelector` strengthens this to the exact spinor form: every
zero-determinant `2x2` tangent matrix factors as `lambda tensor lambdatilde`, so vanishing
on every correspondence-space spinor pair is equivalent to the pure-trace condition.
This is the finite algebraic core of the correspondence-space second-order Einstein-bundle
operator described by LeBrun and later Bailey-type constructions.  The exact holomorphic
bundle/operator identification remains external geometry, not encoded as a differential
operator in Lean.

For backward compatibility, this module also retains the older chosen-polarity/Hodge
coordinate chain.  That chain explicitly chooses the ambient bilinear form
`diag(+,+,-,-)` to identify `V* -> V`; it is optional extra structure and is not part of
the canonical epsilon core.

The rank-four homogeneous degree reflection also retains two tagged interpretations:
cross-side full Fourier `PT* <-> PT` preserves the physical helicity of the momentum
state, whereas the same integer reflection read on one fixed twistor side is the
opposite-helicity bundle degree.  Likewise, the celestial shadow label `J -> -J` must not
be read as Fourier physically manufacturing an opposite-helicity state.

What is NOT proved here:

* a conformally canonical pointwise identification `PT* -> PT` (none is needed for the
  canonical incidence chain);
* the full homogeneous distributional/projective Fourier-Penrose integral theorem in Lean;
* the analytic half-Fourier/light-transform integral intertwiners in Lean;
* generation of an independent second chiral component from one pure chiral field;
* an intrinsic holomorphic construction of LeBrun's rank-two Einstein bundle solely from
  the curved ambitwistor/contact manifold;
* a nonlinear reconstruction theorem showing how generic interacting left/right field
  data are encoded simultaneously as unconstrained intrinsic ambitwistor data.

The nonlinear frontier is therefore sharply localized.  Full conformal geometry already
lives on the single orientation-blind null-geodesic/contact space, and orientation reversal
only swaps its Hodge/Weyl chiral reading.  The genuinely hard googly problem is not this
label swap: it is the intrinsic nonlinear encoding/reconstruction of both interacting
chiral sectors—equivalently, recognizing the Einstein selector and field data directly
inside curved ambitwistor geometry without retreating to one integrable twistor quotient.
-/

namespace GppGooglyGeometryIntertwinerSpine

open GppGrassmannianGooglyDecomposition
open GppFourierSliceSupportGeometry
open GppFourierEpsilonCliffordSupport
open GppFourierDualSplitPolarity
open GppSplitPolarityComplementBridge
open GppSplitSignatureHodgeGrassmannian
open GppKleinSpinorIncidence
open GppTwistorCanonicalShift
open GppTwistorWeightDuality
open GppTwistorRepresentationConvention

/-- Canonical metric-free support theorem: the two Fourier constraints on a graph-plane
slice vanish exactly when the dual Fourier variable lies in the epsilon-Clifford kernel
of the same Klein point. -/
theorem canonical_fourier_support_is_clifford_kernel
    (a b c d : ℝ) (ξ : GppTwistorAnnihilatorIncidence.V4) :
    (phaseConstraint1 a b ξ = 0 ∧ phaseConstraint2 c d ξ = 0) ↔
      cMinus (chartPlucker (a,b,c,d)) ξ = (0,0,0,0) :=
  fourier_constraints_iff_clifford_kernel a b c d ξ

/-- Canonical plane-level companion: epsilon middle-degree duality carries the source
Plucker plane to the annihilator/Fourier-support plane, with no `V* ≅ V` choice. -/
theorem canonical_epsilon_dual_is_fourier_support_plane
    (a b c d : ℝ) :
    GppEpsilonAnnihilatorDuality.epsilonDualPlucker (chartPlucker (a,b,c,d)) =
      GppEpsilonAnnihilatorDuality.annihilatorPlucker a b c d :=
  epsilon_dual_is_fourier_support_plane a b c d

/-- Fourier support constraints become the chosen split metric polarity after the chosen
musical identification, up to the central projective sign.  This theorem is retained as
an optional-coordinate statement, not as part of the canonical epsilon chain. -/
theorem fourier_support_to_split_polarity
    (a b c d : ℝ) (ξ : GppTwistorAnnihilatorIncidence.V4)
    (h1 : phaseConstraint1 a b ξ = 0)
    (h2 : phaseConstraint2 c d ξ = 0) :
    splitSharp ξ =
      scaleV4 (-1)
        (splitDualLineVector a b c d ξ.2.2.1 ξ.2.2.2) :=
  fourier_support_sharp_is_projective_split_polarity a b c d ξ h1 h2

/-- The chosen split polarity row-reduces to the corresponding Hodge/Grassmannian
complement.  This remains a statement about the additional chosen polarity. -/
theorem split_polarity_to_grassmannian
    (a b c d : ℝ) (hD : a*d - b*c ≠ 0) :
    let A : M2 := (a,b,c,d)
    let B := splitComplement A
    splitReducedRow1 a b c d = (1,0,B.1,B.2.1) ∧
    splitReducedRow2 a b c d = (0,1,B.2.2.1,B.2.2.2) :=
  split_polarity_is_hodge_complement a b c d hD

/-- The Grassmannian complement is the normalized split Hodge-star image in Plucker
coordinates for the chosen metric/orientation data. -/
theorem grassmannian_to_split_hodge
    (A : M2) (hD : det2 A ≠ 0) :
    chartPlucker (splitComplement A) =
      let D := det2 A
      ⟨1, (splitStar (chartPlucker A)).p02 / D,
          (splitStar (chartPlucker A)).p03 / D,
          (splitStar (chartPlucker A)).p12 / D,
          (splitStar (chartPlucker A)).p13 / D,
          (splitStar (chartPlucker A)).p23 / D⟩ :=
  chartPlucker_splitComplement A hD

/-- Same-side numerical interpretation: the canonical degree reflection takes the degree
assigned on a fixed convention to `n` into the degree assigned there to `-n`.  This is
a bundle-degree statement, not the cross-side physical interpretation of full Fourier. -/
theorem ambient_four_to_opposite_helicity_degree_same_side (n : ℤ) :
    serreWeight (twistorWeight n) = twistorWeight (-n) :=
  serreWeight_is_helicityFlip n

/-- Backward-compatible name for the same numerical degree theorem.  The theorem is exact;
its name must not be read as saying that cross-side full Fourier flips the physical helicity. -/
theorem ambient_four_to_opposite_helicity (n : ℤ) :
    serreWeight (twistorWeight n) = twistorWeight (-n) :=
  ambient_four_to_opposite_helicity_degree_same_side n

/-- Cross-side physical interpretation: the same rank-four degree reflection maps the
dual-twistor representative to the ordinary-twistor representative with the SAME physical
helicity label. -/
theorem ambient_four_cross_side_same_helicity (n : ℤ) :
    fourierWeight (dualTwistorPhysicalWeight n) = ordinaryTwistorPhysicalWeight n :=
  fourier_dual_to_ordinary_same_helicity n

/-- Original finite-dimensional optional-polarity capstone, retained as an exact
coordinate/degree theorem.  The final conjunct is explicitly the same-side numerical
degree reading. -/
theorem finite_dimensional_googly_spine
    (a b c d : ℝ)
    (ξ : GppTwistorAnnihilatorIncidence.V4)
    (h1 : phaseConstraint1 a b ξ = 0)
    (h2 : phaseConstraint2 c d ξ = 0)
    (hD : a*d - b*c ≠ 0)
    (n : ℤ) :
    splitSharp ξ =
        scaleV4 (-1)
          (splitDualLineVector a b c d ξ.2.2.1 ξ.2.2.2) ∧
    (let A : M2 := (a,b,c,d)
     let B := splitComplement A
     splitReducedRow1 a b c d = (1,0,B.1,B.2.1) ∧
     splitReducedRow2 a b c d = (0,1,B.2.2.1,B.2.2.2)) ∧
    chartPlucker (splitComplement (a,b,c,d)) =
      (let D := det2 (a,b,c,d)
       ⟨1, (splitStar (chartPlucker (a,b,c,d))).p02 / D,
           (splitStar (chartPlucker (a,b,c,d))).p03 / D,
           (splitStar (chartPlucker (a,b,c,d))).p12 / D,
           (splitStar (chartPlucker (a,b,c,d))).p13 / D,
           (splitStar (chartPlucker (a,b,c,d))).p23 / D⟩) ∧
    serreWeight (twistorWeight n) = twistorWeight (-n) := by
  refine ⟨fourier_support_to_split_polarity a b c d ξ h1 h2, ?_, ?_, ?_⟩
  · exact split_polarity_to_grassmannian a b c d hD
  · exact grassmannian_to_split_hodge (a,b,c,d) hD
  · exact ambient_four_to_opposite_helicity_degree_same_side n

/-- Side-aware version of the optional-polarity capstone: the support/polarity/Hodge
coordinate chain is unchanged, while the actual cross-side Fourier degree theorem is
recorded with its same physical helicity label. -/
theorem finite_dimensional_googly_spine_side_aware
    (a b c d : ℝ)
    (ξ : GppTwistorAnnihilatorIncidence.V4)
    (h1 : phaseConstraint1 a b ξ = 0)
    (h2 : phaseConstraint2 c d ξ = 0)
    (hD : a*d - b*c ≠ 0)
    (n : ℤ) :
    splitSharp ξ =
        scaleV4 (-1)
          (splitDualLineVector a b c d ξ.2.2.1 ξ.2.2.2) ∧
    (let A : M2 := (a,b,c,d)
     let B := splitComplement A
     splitReducedRow1 a b c d = (1,0,B.1,B.2.1) ∧
     splitReducedRow2 a b c d = (0,1,B.2.2.1,B.2.2.2)) ∧
    chartPlucker (splitComplement (a,b,c,d)) =
      (let D := det2 (a,b,c,d)
       ⟨1, (splitStar (chartPlucker (a,b,c,d))).p02 / D,
           (splitStar (chartPlucker (a,b,c,d))).p03 / D,
           (splitStar (chartPlucker (a,b,c,d))).p12 / D,
           (splitStar (chartPlucker (a,b,c,d))).p13 / D,
           (splitStar (chartPlucker (a,b,c,d))).p23 / D⟩) ∧
    fourierWeight (dualTwistorPhysicalWeight n) = ordinaryTwistorPhysicalWeight n := by
  refine ⟨fourier_support_to_split_polarity a b c d ξ h1 h2, ?_, ?_, ?_⟩
  · exact split_polarity_to_grassmannian a b c d hD
  · exact grassmannian_to_split_hodge (a,b,c,d) hD
  · exact ambient_four_cross_side_same_helicity n

end GppGooglyGeometryIntertwinerSpine
