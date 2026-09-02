import Mathlib.Tactic
import GppVerify.CelestialHolography.GrassmannianGooglyDecomposition

/-!
# Twistor annihilator incidence on the Gr(2,4) big cell

A point of complexified compactified spacetime is a projective twistor line, hence a
2-plane in a 4-dimensional twistor vector space.  The natural dual operation on such a
line is not a pointwise map `PT -> PT*`; it is the annihilator-plane construction

  W  |->  W^0 subset V*.

For the graph plane `[I|A]`, this annihilator is represented before row reduction by
`[-A^T|I]`.  When `det A != 0`, row reduction gives `[I|-A^{-T}]`, exactly the
`complement` map formalized in `GrassmannianGooglyDecomposition.lean`.

This is the finite-dimensional incidence statement needed before any Penrose-transform
or cohomological googly claim.  It also exposes an important structural fact: complement
duality acts canonically on twistor *lines* (Gr(2,4)), not on individual projective
twistors.  A field-level googly operation therefore has to be a correspondence/integral
intertwiner unless additional structure supplies a pointwise PT-to-PT* map.
-/

namespace GppTwistorAnnihilatorIncidence

abbrev V4 := ℝ × ℝ × ℝ × ℝ

/-- Standard bilinear pairing between a row vector and a dual row vector. -/
def pair4 (x y : V4) : ℝ :=
  x.1*y.1 + x.2.1*y.2.1 + x.2.2.1*y.2.2.1 + x.2.2.2*y.2.2.2

/-- First spanning vector of the graph plane `[I|A]`. -/
def graphRow1 (a b : ℝ) : V4 := (1,0,a,b)

/-- Second spanning vector of the graph plane `[I|A]`. -/
def graphRow2 (c d : ℝ) : V4 := (0,1,c,d)

/-- First canonical annihilator covector of `[I|A]`: (-a,-c,1,0). -/
def annihilator1 (a c : ℝ) : V4 := (-a,-c,1,0)

/-- Second canonical annihilator covector of `[I|A]`: (-b,-d,0,1). -/
def annihilator2 (b d : ℝ) : V4 := (-b,-d,0,1)

/-- The first annihilator basis vector annihilates the first graph row. -/
theorem ann1_row1 (a b c : ℝ) :
    pair4 (graphRow1 a b) (annihilator1 a c) = 0 := by
  simp [pair4, graphRow1, annihilator1]

/-- The first annihilator basis vector annihilates the second graph row. -/
theorem ann1_row2 (a c d : ℝ) :
    pair4 (graphRow2 c d) (annihilator1 a c) = 0 := by
  simp [pair4, graphRow2, annihilator1]

/-- The second annihilator basis vector annihilates the first graph row. -/
theorem ann2_row1 (a b d : ℝ) :
    pair4 (graphRow1 a b) (annihilator2 b d) = 0 := by
  simp [pair4, graphRow1, annihilator2]

/-- The second annihilator basis vector annihilates the second graph row. -/
theorem ann2_row2 (b c d : ℝ) :
    pair4 (graphRow2 c d) (annihilator2 b d) = 0 := by
  simp [pair4, graphRow2, annihilator2]

/-- The two displayed annihilator vectors are linearly independent: if a linear
combination vanishes, its coefficients vanish.  Components 3 and 4 witness this
directly. -/
theorem annihilator_basis_independent (a b c d α β : ℝ)
    (h : (α*(-a) + β*(-b), α*(-c) + β*(-d), α, β) = ((0:ℝ),0,0,0)) :
    α = 0 ∧ β = 0 := by
  have h3 : α = 0 := by
    exact congrArg (fun x : V4 => x.2.2.1) h
  have h4 : β = 0 := by
    exact congrArg (fun x : V4 => x.2.2.2) h
  exact ⟨h3,h4⟩

/-- In coordinates, the annihilator plane is `[-A^T|I]`.  Its left 2x2 block
has the same determinant as `A`. -/
theorem annihilator_left_block_det (a b c d : ℝ) :
    (-a)*(-d) - (-c)*(-b) = a*d - b*c := by ring

/-- The row-reduced right block of `[-A^T|I]` is exactly `-A^{-T}`, i.e. the
`complement` chart map.  This theorem records the four entries explicitly. -/
theorem row_reduced_annihilator_is_complement
    (a b c d : ℝ) (hD : a*d-b*c ≠ 0) :
    GppGrassmannianGooglyDecomposition.complement (a,b,c,d)
      = (-d/(a*d-b*c), c/(a*d-b*c), b/(a*d-b*c), -a/(a*d-b*c)) := by
  rfl

/-- No canonical pointwise dual twistor is selected by the annihilator plane alone:
there are always at least the two distinct displayed annihilator directions. -/
theorem annihilator_directions_distinct (a b c d : ℝ) :
    annihilator1 a c ≠ annihilator2 b d := by
  intro h
  have h3 := congrArg (fun x : V4 => x.2.2.1) h
  norm_num [annihilator1, annihilator2] at h3

end GppTwistorAnnihilatorIncidence
