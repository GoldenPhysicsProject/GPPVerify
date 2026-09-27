import Mathlib.Tactic
import GppVerify.CelestialHolography.AnnihilatorComplementBridge
import GppVerify.CelestialHolography.GrassmannianGooglyDecomposition
import GppVerify.CelestialHolography.TwistorCanonicalShift

/-!
# Concrete ambient-four googly duality spine

This module closes a finite-dimensional part of the proposed identification

  D_flag  ~  D_Gr  ~  D_Hodge.

On the invertible big cell of Gr(2,4):

* Penrose-flag annihilator duality row-reduces to `A -> -A^{-T}`;
* the same chart complement is the normalized Plucker/Hodge star operation;
* independently, ambient complex rank four forces the projective canonical shift
  `k -> -k-4`, hence opposite helicity weight.

The first two statements are now literally the same coordinate operation, not merely
analogous formulas.  The final step to a field/cohomology Penrose intertwiner remains
analytic and is not asserted here.
-/

namespace GppConcreteGooglyDualitySpine

open GppAnnihilatorComplementBridge
open GppGrassmannianGooglyDecomposition
open GppTwistorCanonicalShift
open GppTwistorWeightDuality

/-- Flag annihilation and Grassmannian complement agree on the invertible big cell. -/
theorem flag_duality_eq_grassmannian_complement
    (a b c d : ℝ) (hD : a*d - b*c ≠ 0) :
    let A : M2 := (a,b,c,d)
    let B := complement A
    reducedDualRow1 a b c d = (1,0,B.1,B.2.1) ∧
    reducedDualRow2 a b c d = (0,1,B.2.2.1,B.2.2.2) :=
  annihilator_is_grassmannian_complement a b c d hD

/-- The same complement is the normalized Plucker-star image in chart coordinates. -/
theorem grassmannian_complement_eq_normalized_plucker_star
    (A : M2) (hD : det2 A ≠ 0) :
    chartPlucker (complement A) =
      let D := det2 A
      ⟨1, (pluckerStar (chartPlucker A)).p02 / D,
          (pluckerStar (chartPlucker A)).p03 / D,
          (pluckerStar (chartPlucker A)).p12 / D,
          (pluckerStar (chartPlucker A)).p13 / D,
          (pluckerStar (chartPlucker A)).p23 / D⟩ :=
  chartPlucker_complement A hD

/-- Finite-dimensional capstone: on an invertible chart, the annihilator-dual plane
is represented by the same complement whose Plucker coordinates are the normalized
Hodge-star coordinates. -/
theorem flag_grassmannian_hodge_same_chart_operation
    (a b c d : ℝ) (hD : a*d - b*c ≠ 0) :
    let A : M2 := (a,b,c,d)
    let B := complement A
    (reducedDualRow1 a b c d = (1,0,B.1,B.2.1) ∧
     reducedDualRow2 a b c d = (0,1,B.2.2.1,B.2.2.2)) ∧
    chartPlucker B =
      let D := det2 A
      ⟨1, (pluckerStar (chartPlucker A)).p02 / D,
          (pluckerStar (chartPlucker A)).p03 / D,
          (pluckerStar (chartPlucker A)).p12 / D,
          (pluckerStar (chartPlucker A)).p13 / D,
          (pluckerStar (chartPlucker A)).p23 / D⟩ := by
  dsimp only
  constructor
  · exact annihilator_is_grassmannian_complement a b c d hD
  · exact chartPlucker_complement (a,b,c,d) hD

/-- The projective rank-four canonical reflection attached to the same ambient
four-dimensional setting maps every ordinary twistor helicity weight to the opposite
helicity weight. -/
theorem ambient_four_weight_flip (n : ℤ) :
    serreWeight (twistorWeight n) = twistorWeight (-n) :=
  serreWeight_is_helicityFlip n

/-- For gravity the corresponding homogeneous pair is exactly O(2) <-> O(-6). -/
theorem ambient_four_graviton_pair :
    serreWeight 2 = -6 ∧ serreWeight (-6) = 2 :=
  graviton_weight_pair

end GppConcreteGooglyDualitySpine
