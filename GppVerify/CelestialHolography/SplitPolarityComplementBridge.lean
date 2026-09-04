import Mathlib.Tactic
import GppVerify.CelestialHolography.TwistorAnnihilatorIncidence
import GppVerify.CelestialHolography.SplitSignatureHodgeGrassmannian

/-!
# Split-signature polarity and the Grassmannian complement

For the split bilinear form diag(+,+,-,-), the orthogonal complement of the graph
plane `[I|A]` has canonical basis `[A^T|I]`.  When `det A != 0`, row reduction gives
`[I|A^{-T}]`.

This identifies the split-signature Grassmannian complement `splitComplement(A)` with
metric polarity itself.  The sign difference from the standard annihilator
`[-A^T|I] -> [I|-A^{-T}]` is therefore entirely the choice of bilinear form/reality
structure, not a discrepancy in the underlying duality construction.
-/

namespace GppSplitPolarityComplementBridge

open GppTwistorAnnihilatorIncidence
open GppGrassmannianGooglyDecomposition
open GppSplitSignatureHodgeGrassmannian

/-- Split-signature bilinear pairing with metric diag(+,+,-,-). -/
def splitPair4 (x y : V4) : ℝ :=
  x.1*y.1 + x.2.1*y.2.1 - x.2.2.1*y.2.2.1 - x.2.2.2*y.2.2.2

/-- Canonical split-orthogonal direction corresponding to the third coordinate. -/
def splitOrthogonal1 (a c : ℝ) : V4 := (a,c,1,0)

/-- Canonical split-orthogonal direction corresponding to the fourth coordinate. -/
def splitOrthogonal2 (b d : ℝ) : V4 := (b,d,0,1)

/-- The first split-orthogonal direction is orthogonal to both graph-plane rows. -/
theorem splitOrthogonal1_annihilates_graph
    (a b c d : ℝ) :
    splitPair4 (graphRow1 a b) (splitOrthogonal1 a c) = 0 ∧
    splitPair4 (graphRow2 c d) (splitOrthogonal1 a c) = 0 := by
  constructor <;> simp [splitPair4, graphRow1, graphRow2, splitOrthogonal1]

/-- The second split-orthogonal direction is likewise orthogonal to the graph plane. -/
theorem splitOrthogonal2_annihilates_graph
    (a b c d : ℝ) :
    splitPair4 (graphRow1 a b) (splitOrthogonal2 b d) = 0 ∧
    splitPair4 (graphRow2 c d) (splitOrthogonal2 b d) = 0 := by
  constructor <;> simp [splitPair4, graphRow1, graphRow2, splitOrthogonal2]

/-- General graph-line and split-dual-line vectors are mutually orthogonal. -/
theorem split_line_dualLine_pair_zero
    (a b c d r s t u : ℝ) :
    let x : V4 := (r,s,r*a+s*c,r*b+s*d)
    let y : V4 := (t*a+u*b,t*c+u*d,t,u)
    splitPair4 x y = 0 := by
  simp [splitPair4]
  ring

/-- First row of the row-reduced split-orthogonal plane. -/
def splitReducedRow1 (a b c d : ℝ) : V4 :=
  let D := a*d - b*c
  (1,0,d/D,-c/D)

/-- Second row of the row-reduced split-orthogonal plane. -/
def splitReducedRow2 (a b c d : ℝ) : V4 :=
  let D := a*d - b*c
  (0,1,-b/D,a/D)

/-- Row reduction of `[A^T|I]` produces the first row of `[I|A^{-T}]`. -/
theorem splitReducedRow1_from_orthogonals
    (a b c d : ℝ) (hD : a*d - b*c ≠ 0) :
    splitReducedRow1 a b c d =
      let D := a*d - b*c
      ((d/D) * (splitOrthogonal1 a c).1 + (-c/D) * (splitOrthogonal2 b d).1,
       (d/D) * (splitOrthogonal1 a c).2.1 + (-c/D) * (splitOrthogonal2 b d).2.1,
       (d/D) * (splitOrthogonal1 a c).2.2.1 + (-c/D) * (splitOrthogonal2 b d).2.2.1,
       (d/D) * (splitOrthogonal1 a c).2.2.2 + (-c/D) * (splitOrthogonal2 b d).2.2.2) := by
  simp only [splitReducedRow1, splitOrthogonal1, splitOrthogonal2]
  field_simp [hD]
  <;> ring

/-- Row reduction produces the second row of `[I|A^{-T}]`. -/
theorem splitReducedRow2_from_orthogonals
    (a b c d : ℝ) (hD : a*d - b*c ≠ 0) :
    splitReducedRow2 a b c d =
      let D := a*d - b*c
      ((-b/D) * (splitOrthogonal1 a c).1 + (a/D) * (splitOrthogonal2 b d).1,
       (-b/D) * (splitOrthogonal1 a c).2.1 + (a/D) * (splitOrthogonal2 b d).2.1,
       (-b/D) * (splitOrthogonal1 a c).2.2.1 + (a/D) * (splitOrthogonal2 b d).2.2.1,
       (-b/D) * (splitOrthogonal1 a c).2.2.2 + (a/D) * (splitOrthogonal2 b d).2.2.2) := by
  simp only [splitReducedRow2, splitOrthogonal1, splitOrthogonal2]
  field_simp [hD]
  <;> ring

/-- The right block of the row-reduced split polarity is exactly the existing
split Hodge complement `A^{-T}`. -/
theorem split_polarity_block_eq_splitComplement
    (a b c d : ℝ) :
    let A : M2 := (a,b,c,d)
    let r1 := splitReducedRow1 a b c d
    let r2 := splitReducedRow2 a b c d
    (r1.2.2.1,r1.2.2.2,r2.2.2.1,r2.2.2.2) = splitComplement A := by
  simp [splitReducedRow1, splitReducedRow2, splitComplement, det2]

/-- Main split-signature coordinate bridge: metric polarity and split Hodge
complement are the same big-cell map. -/
theorem split_polarity_is_hodge_complement
    (a b c d : ℝ) (hD : a*d - b*c ≠ 0) :
    let A : M2 := (a,b,c,d)
    let B := splitComplement A
    splitReducedRow1 a b c d = (1,0,B.1,B.2.1) ∧
    splitReducedRow2 a b c d = (0,1,B.2.2.1,B.2.2.2) := by
  simp only [splitReducedRow1, splitReducedRow2, splitComplement, det2]
  constructor <;> field_simp [hD] <;> ring

end GppSplitPolarityComplementBridge
