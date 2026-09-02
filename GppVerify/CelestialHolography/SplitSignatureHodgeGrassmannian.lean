import Mathlib.Tactic
import GppVerify.CelestialHolography.GrassmannianGooglyDecomposition

/-!
# Split-signature Hodge star on Gr(2,4)

The Hodge matrix depends on the real form.  For the split metric
`diag(+,+,-,-)` and orientation `e0∧e1∧e2∧e3`, the action on the ordered
2-form/Plucker basis `(01,02,03,12,13,23)` is

  *01 = 23,   *23 = 01,
  *02 = 13,   *13 = 02,
  *03 = -12,  *12 = -03.

Thus `*^2=+1` over the reals, as required in signature `(2,2)`.
On the graph chart `[I|A]`, this split Hodge complement induces

  C_split(A) = A^{-T},

not the Euclidean-signature chart map `-A^{-T}`.  The existing order-four map
`tau(A)=A epsilon/det(A)` then factors as a fixed quarter-turn after this split
complement.  This file makes the signature dependence explicit.
-/

namespace GppSplitSignatureHodgeGrassmannian

open GppGrassmannianGooglyDecomposition

/-- Split-signature Hodge star in the Plucker basis `(01,02,03,12,13,23)`. -/
def splitStar (p : P6) : P6 :=
  ⟨p.p23, p.p13, -p.p12, -p.p03, p.p02, p.p01⟩

/-- In signature `(2,2)`, the Hodge star squares to `+1` on real two-forms. -/
theorem splitStar_sq (p : P6) : splitStar (splitStar p) = p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rfl

/-- The split Hodge star preserves the Klein/Plucker quadric. -/
theorem kleinQ_splitStar (p : P6) : kleinQ (splitStar p) = kleinQ p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [kleinQ, splitStar]
  ring

/-- Split-signature self-dual coordinates. -/
def s1 (p : P6) : ℝ := (p.p01 + p.p23) / 2
def s2 (p : P6) : ℝ := (p.p02 + p.p13) / 2
def s3 (p : P6) : ℝ := (p.p03 - p.p12) / 2

/-- Split-signature anti-self-dual coordinates. -/
def a1 (p : P6) : ℝ := (p.p01 - p.p23) / 2
def a2 (p : P6) : ℝ := (p.p02 - p.p13) / 2
def a3 (p : P6) : ℝ := (p.p03 + p.p12) / 2

/-- Split Hodge fixes the three SD coordinates. -/
theorem splitStar_fixes_sd (p : P6) :
    s1 (splitStar p) = s1 p ∧
    s2 (splitStar p) = s2 p ∧
    s3 (splitStar p) = s3 p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [s1,s2,s3,splitStar]
  constructor
  · ring
  · constructor <;> ring

/-- Split Hodge negates the three ASD coordinates. -/
theorem splitStar_negates_asd (p : P6) :
    a1 (splitStar p) = -a1 p ∧
    a2 (splitStar p) = -a2 p ∧
    a3 (splitStar p) = -a3 p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [a1,a2,a3,splitStar]
  constructor
  · ring
  · constructor <;> ring

/-- On the big cell, split Hodge complement is `A^{-T}`. -/
noncomputable def splitComplement (A : M2) : M2 :=
  let D := det2 A
  (A.2.2.2 / D, -A.2.2.1 / D, -A.2.1 / D, A.1 / D)

/-- Its determinant is reciprocal. -/
theorem det2_splitComplement (A : M2) (hD : det2 A ≠ 0) :
    det2 (splitComplement A) = 1 / det2 A := by
  rcases A with ⟨a,b,c,d⟩
  simp only [det2, splitComplement] at hD ⊢
  field_simp [hD]
  ring

/-- Split complement is an involution on the invertible big cell. -/
theorem splitComplement_involutive (A : M2) (hD : det2 A ≠ 0) :
    splitComplement (splitComplement A) = A := by
  rcases A with ⟨a,b,c,d⟩
  simp only [det2, splitComplement] at hD ⊢
  have hrecip : d * a - c * b ≠ 0 := by
    nlinarith
  field_simp [hD, hrecip]
  <;> ring

/-- Split Hodge of a graph-plane Plucker vector is exactly the split complementary
plane after projective normalization by `det A`. -/
theorem chartPlucker_splitComplement (A : M2) (hD : det2 A ≠ 0) :
    chartPlucker (splitComplement A) =
      let D := det2 A
      ⟨1, (splitStar (chartPlucker A)).p02 / D,
          (splitStar (chartPlucker A)).p03 / D,
          (splitStar (chartPlucker A)).p12 / D,
          (splitStar (chartPlucker A)).p13 / D,
          (splitStar (chartPlucker A)).p23 / D⟩ := by
  rcases A with ⟨a,b,c,d⟩
  simp only [chartPlucker, splitComplement, det2, splitStar]
  ext <;> simp
  · field_simp [hD]
    ring

/-- Fixed quarter-turn compatible with the sign convention above. -/
def splitQuarterTurn (A : M2) : M2 :=
  (-A.2.1, A.1, -A.2.2.2, A.2.2.1)

/-- The split quarter-turn squares to the central minus sign. -/
theorem splitQuarterTurn_sq (A : M2) :
    splitQuarterTurn (splitQuarterTurn A) = (-A.1,-A.2.1,-A.2.2.1,-A.2.2.2) := by
  rcases A with ⟨a,b,c,d⟩
  rfl

/-- The existing Grassmannian `tau` factors through the genuine split-signature
Hodge complement. -/
theorem tau_eq_splitQuarterTurn_splitComplement (A : M2) :
    tau A = splitQuarterTurn (splitComplement A) := by
  rcases A with ⟨a,b,c,d⟩
  rfl

end GppSplitSignatureHodgeGrassmannian
