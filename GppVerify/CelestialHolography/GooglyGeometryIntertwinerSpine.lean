import Mathlib.Tactic
import GppVerify.CelestialHolography.FourierEpsilonCliffordSupport
import GppVerify.CelestialHolography.FlatInfinityChiralComplex
import GppVerify.CelestialHolography.FlatInfinityCelestialFactorization
import GppVerify.CelestialHolography.CelestialLightWeylIntertwiners
import GppVerify.CelestialHolography.PrincipalSeriesLightPlancherelMatch
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
therefore not identified with shadow.  `PrincipalSeriesLightPlancherelMatch` records the
exact closed-form normalization relation to the odd real principal-series density.

For backward compatibility, this module also retains the older chosen-polarity/Hodge
coordinate chain.  That chain explicitly chooses the ambient bilinear form
`diag(+,+,-,-)` to identify `V* -> V`; it is optional extra structure and is not part of
the canonical epsilon core.

The rank-four homogeneous degree reflection also retains two tagged interpretations:
cross-side full Fourier `PT* <-> PT` preserves the physical helicity of the momentum
state, whereas the same integer reflection read on one fixed twistor side is the
opposite-helicity bundle degree.

What is NOT proved here:

* a conformally canonical pointwise identification `PT* -> PT` (none is needed for the
  canonical incidence chain);
* the full homogeneous distributional/projective Fourier-Penrose integral theorem in Lean;
* the analytic half-Fourier/light-transform integral intertwiner in Lean;
* a physical orientation reversal from the optional polarity map;
* generation of an independent second chiral component from one pure chiral field;
* the nonlinear Einstein selector on full ambitwistor/contact data.

The last item is now the principal nonlinear frontier: the finite-dimensional algebra
naturally points to ambidextrous twistor/dual-twistor incidence rather than a deterministic
map from one chirality to the other.
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
