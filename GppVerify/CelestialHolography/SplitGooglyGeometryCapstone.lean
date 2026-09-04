import Mathlib.Tactic
import GppVerify.CelestialHolography.SplitPolarityComplementBridge
import GppVerify.CelestialHolography.SplitSignatureHodgeGrassmannian

/-!
# Split-signature googly geometry capstone

This module packages the exact finite-dimensional split-signature identifications:

  metric polarity = Grassmannian complement = normalized split Hodge star,

and the existing order-four Grassmannian map factors as

  tau = quarterTurn o polarity.

Thus the order-four lift is not the Hodge/polarity involution itself.  It is that
involution composed with a fixed quarter-turn whose square is the central sign.
This keeps the previously observed order-two Fourier/Hodge behavior distinct from the
order-four Grassmannian lift.
-/

namespace GppSplitGooglyGeometryCapstone

open GppGrassmannianGooglyDecomposition
open GppSplitSignatureHodgeGrassmannian
open GppSplitPolarityComplementBridge

/-- Split metric polarity and split Hodge complement are literally the same big-cell
map, and its Plucker image is the normalized split Hodge star. -/
theorem polarity_grassmannian_hodge_chain
    (a b c d : ℝ) (hD : a*d - b*c ≠ 0) :
    let A : M2 := (a,b,c,d)
    let B := splitComplement A
    (splitReducedRow1 a b c d = (1,0,B.1,B.2.1) ∧
     splitReducedRow2 a b c d = (0,1,B.2.2.1,B.2.2.2)) ∧
    chartPlucker B =
      let D := det2 A
      ⟨1, (splitStar (chartPlucker A)).p02 / D,
          (splitStar (chartPlucker A)).p03 / D,
          (splitStar (chartPlucker A)).p12 / D,
          (splitStar (chartPlucker A)).p13 / D,
          (splitStar (chartPlucker A)).p23 / D⟩ := by
  dsimp only
  constructor
  · exact split_polarity_is_hodge_complement a b c d hD
  · exact chartPlucker_splitComplement (a,b,c,d) hD

/-- The Grassmannian order-four map is the fixed quarter-turn after split metric
polarity/Hodge complement. -/
theorem tau_is_quarterTurn_after_polarity (A : M2) :
    tau A = splitQuarterTurn (splitComplement A) :=
  tau_eq_splitQuarterTurn_splitComplement A

/-- Polarity/Hodge itself is involutive on the invertible chart. -/
theorem polarity_is_involution (A : M2) (hD : det2 A ≠ 0) :
    splitComplement (splitComplement A) = A :=
  splitComplement_involutive A hD

/-- The fixed quarter-turn squares to the central sign. -/
theorem quarterTurn_sq_is_central_minus (A : M2) :
    splitQuarterTurn (splitQuarterTurn A) =
      (-A.1,-A.2.1,-A.2.2.1,-A.2.2.2) :=
  splitQuarterTurn_sq A

/-- Consequently the lifted Grassmannian map squares to the central sign, while the
underlying polarity remains order two. -/
theorem tau_sq_is_central_minus
    (A : M2) (hD : det2 A ≠ 0) :
    tau (tau A) = (-A.1,-A.2.1,-A.2.2.1,-A.2.2.2) :=
  tau_sq_from_split_hodge A hD

end GppSplitGooglyGeometryCapstone
