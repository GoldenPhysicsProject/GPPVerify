import Mathlib.Tactic
import GppVerify.CelestialHolography.FourierDualSplitPolarity
import GppVerify.CelestialHolography.SplitGooglyGeometryCapstone
import GppVerify.CelestialHolography.TwistorCanonicalShift

/-!
# Googly geometry intertwiner spine

This file packages the strongest exact part of the GPP googly construction currently
available.  Starting from the support constraints produced by restricting the
four-dimensional Fourier phase to a twistor 2-plane, one obtains:

1. the ordinary annihilator plane in Fourier-dual space;
2. after the split musical identification `V* -> V`, the split metric-polarity plane,
   up to the central projective sign;
3. after big-cell row reduction, the split Grassmannian complement `A^{-T}`;
4. in Plucker coordinates, the normalized split Hodge star;
5. in projective twistor homogeneity, the ambient rank-four canonical reflection
   `k -> -k-4`, i.e. opposite helicity weight.

Thus the finite-dimensional support geometry behind

  D_Fourier ~ D_polarity ~ D_Gr ~ D_Hodge

is explicit.  What is NOT proved here is the remaining analytic/projective theorem
that the homogeneous distributional Fourier transform and the projective X-ray/Penrose
integrals obey the corresponding commuting square on field classes.
-/

namespace GppGooglyGeometryIntertwinerSpine

open GppGrassmannianGooglyDecomposition
open GppFourierSliceSupportGeometry
open GppFourierDualSplitPolarity
open GppSplitPolarityComplementBridge
open GppSplitSignatureHodgeGrassmannian
open GppTwistorCanonicalShift
open GppTwistorWeightDuality

/-- Fourier support constraints become split metric polarity after the split musical
identification, up to the central projective sign. -/
theorem fourier_support_to_split_polarity
    (a b c d : ℝ) (ξ : GppTwistorAnnihilatorIncidence.V4)
    (h1 : phaseConstraint1 a b ξ = 0)
    (h2 : phaseConstraint2 c d ξ = 0) :
    splitSharp ξ =
      scaleV4 (-1)
        (splitDualLineVector a b c d ξ.2.2.1 ξ.2.2.2) :=
  fourier_support_sharp_is_projective_split_polarity a b c d ξ h1 h2

/-- Split polarity row-reduces to the split Hodge/Grassmannian complement. -/
theorem split_polarity_to_grassmannian
    (a b c d : ℝ) (hD : a*d - b*c ≠ 0) :
    let A : M2 := (a,b,c,d)
    let B := splitComplement A
    splitReducedRow1 a b c d = (1,0,B.1,B.2.1) ∧
    splitReducedRow2 a b c d = (0,1,B.2.2.1,B.2.2.2) :=
  split_polarity_is_hodge_complement a b c d hD

/-- The Grassmannian complement is the normalized split Hodge-star image in Plucker
coordinates. -/
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

/-- Independently, ambient complex rank four forces the canonical projective weight
reflection to be the opposite-helicity weight. -/
theorem ambient_four_to_opposite_helicity (n : ℤ) :
    serreWeight (twistorWeight n) = twistorWeight (-n) :=
  serreWeight_is_helicityFlip n

/-- Capstone bundle of the exact geometric and homogeneous statements. -/
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
  · exact ambient_four_to_opposite_helicity n

end GppGooglyGeometryIntertwinerSpine
