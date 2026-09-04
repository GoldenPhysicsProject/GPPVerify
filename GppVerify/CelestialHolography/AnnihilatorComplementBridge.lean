import Mathlib.Tactic
import GppVerify.CelestialHolography.TwistorAnnihilatorIncidence
import GppVerify.CelestialHolography.GrassmannianGooglyDecomposition

/-!
# Annihilator/complement bridge on the Gr(2,4) big cell

For a graph plane represented by `[I | A]`, with

  A = [[a,b],[c,d]],

its annihilator in the dual four-space has the canonical row basis

  [-A^T | I].

When `det A != 0`, row-reducing this dual plane back to the standard big-cell chart
`[I | B]` gives

  B = (-A^T)^(-1) = -A^(-T).

Thus the Euclidean Grassmannian complement used elsewhere in the formalization is not
an unrelated chart trick: it is exactly annihilator duality expressed in the same
`[I | A]` coordinates.  This is a finite-dimensional bridge between the Penrose flag
annihilator and the Grassmannian googly/complement map.
-/

namespace GppAnnihilatorComplementBridge

open GppTwistorAnnihilatorIncidence
open GppGrassmannianGooglyDecomposition

/-- First row of the row-reduced annihilator plane. -/
def reducedDualRow1 (a b c d : ℝ) : V4 :=
  let D := a*d - b*c
  (1, 0, -d / D, c / D)

/-- Second row of the row-reduced annihilator plane. -/
def reducedDualRow2 (a b c d : ℝ) : V4 :=
  let D := a*d - b*c
  (0, 1, b / D, -a / D)

/-- The first reduced row is the explicit linear combination of the two canonical
annihilator directions with coefficients `(-d/D,c/D)`. -/
theorem reducedDualRow1_from_annihilators
    (a b c d : ℝ) (hD : a*d - b*c ≠ 0) :
    reducedDualRow1 a b c d =
      let D := a*d - b*c
      ((-d/D) * (annihilator1 a c).1 + (c/D) * (annihilator2 b d).1,
       (-d/D) * (annihilator1 a c).2.1 + (c/D) * (annihilator2 b d).2.1,
       (-d/D) * (annihilator1 a c).2.2.1 + (c/D) * (annihilator2 b d).2.2.1,
       (-d/D) * (annihilator1 a c).2.2.2 + (c/D) * (annihilator2 b d).2.2.2) := by
  simp only [reducedDualRow1, annihilator1, annihilator2]
  field_simp [hD]
  <;> ring

/-- The second reduced row is the explicit linear combination with coefficients
`(b/D,-a/D)`. -/
theorem reducedDualRow2_from_annihilators
    (a b c d : ℝ) (hD : a*d - b*c ≠ 0) :
    reducedDualRow2 a b c d =
      let D := a*d - b*c
      ((b/D) * (annihilator1 a c).1 + (-a/D) * (annihilator2 b d).1,
       (b/D) * (annihilator1 a c).2.1 + (-a/D) * (annihilator2 b d).2.1,
       (b/D) * (annihilator1 a c).2.2.1 + (-a/D) * (annihilator2 b d).2.2.1,
       (b/D) * (annihilator1 a c).2.2.2 + (-a/D) * (annihilator2 b d).2.2.2) := by
  simp only [reducedDualRow2, annihilator1, annihilator2]
  field_simp [hD]
  <;> ring

/-- The right-hand 2x2 block of the row-reduced annihilator is exactly the existing
Euclidean complement `-A^{-T}`. -/
theorem reduced_annihilator_block_eq_complement
    (a b c d : ℝ) :
    let A : M2 := (a,b,c,d)
    let r1 := reducedDualRow1 a b c d
    let r2 := reducedDualRow2 a b c d
    (r1.2.2.1, r1.2.2.2, r2.2.2.1, r2.2.2.2) = complement A := by
  simp [reducedDualRow1, reducedDualRow2, complement, det2]

/-- Consequently annihilator duality and the Grassmannian complement are the same
big-cell operation whenever `det A != 0`: the canonical dual basis `[-A^T|I]` row
reduces to `[I|-A^{-T}]`. -/
theorem annihilator_is_grassmannian_complement
    (a b c d : ℝ) (hD : a*d - b*c ≠ 0) :
    let A : M2 := (a,b,c,d)
    let B := complement A
    reducedDualRow1 a b c d = (1,0,B.1,B.2.1) ∧
    reducedDualRow2 a b c d = (0,1,B.2.2.1,B.2.2.2) := by
  simp only [reducedDualRow1, reducedDualRow2, complement, det2]
  constructor <;> field_simp [hD] <;> ring

end GppAnnihilatorComplementBridge
