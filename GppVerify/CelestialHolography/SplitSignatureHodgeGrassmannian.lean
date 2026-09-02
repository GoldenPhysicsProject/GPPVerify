import Mathlib.Tactic
import GppVerify.CelestialHolography.GrassmannianGooglyDecomposition

/-!
# Split-signature Hodge star on Gr(2,4)

For the split metric `diag(+,+,-,-)` and orientation `e0∧e1∧e2∧e3`, the Hodge
star on the ordered Plucker basis `(01,02,03,12,13,23)` is

  *01 = 23,   *23 = 01,
  *02 = 13,   *13 = 02,
  *03 = -12,  *12 = -03.

Thus `*^2=+1` over the reals.  On the graph chart `[I|A]`, split Hodge complement
induces `C_split(A)=A^{-T}`.  This differs by a central sign from the Euclidean
chart convention `-A^{-T}` used elsewhere, so the signature choice matters.
-/

namespace GppSplitSignatureHodgeGrassmannian

open GppGrassmannianGooglyDecomposition

def splitStar (p : P6) : P6 :=
  ⟨p.p23, p.p13, -p.p12, -p.p03, p.p02, p.p01⟩

theorem splitStar_sq (p : P6) : splitStar (splitStar p) = p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rfl

theorem kleinQ_splitStar (p : P6) : kleinQ (splitStar p) = kleinQ p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [kleinQ, splitStar]
  ring

def s1 (p : P6) : ℝ := (p.p01 + p.p23) / 2
def s2 (p : P6) : ℝ := (p.p02 + p.p13) / 2
def s3 (p : P6) : ℝ := (p.p03 - p.p12) / 2

def a1 (p : P6) : ℝ := (p.p01 - p.p23) / 2
def a2 (p : P6) : ℝ := (p.p02 - p.p13) / 2
def a3 (p : P6) : ℝ := (p.p03 + p.p12) / 2

theorem splitStar_fixes_sd (p : P6) :
    s1 (splitStar p) = s1 p ∧
    s2 (splitStar p) = s2 p ∧
    s3 (splitStar p) = s3 p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [s1,s2,s3,splitStar]
  constructor
  · ring
  · constructor <;> ring

theorem splitStar_negates_asd (p : P6) :
    a1 (splitStar p) = -a1 p ∧
    a2 (splitStar p) = -a2 p ∧
    a3 (splitStar p) = -a3 p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [a1,a2,a3,splitStar]
  constructor
  · ring
  · constructor <;> ring

noncomputable def splitComplement (A : M2) : M2 :=
  let D := det2 A
  (A.2.2.2 / D, -A.2.2.1 / D, -A.2.1 / D, A.1 / D)

theorem det2_splitComplement (A : M2) (hD : det2 A ≠ 0) :
    det2 (splitComplement A) = 1 / det2 A := by
  rcases A with ⟨a,b,c,d⟩
  simp only [det2, splitComplement] at hD ⊢
  field_simp [hD]
  ring

theorem splitComplement_involutive (A : M2) (hD : det2 A ≠ 0) :
    splitComplement (splitComplement A) = A := by
  rcases A with ⟨a,b,c,d⟩
  simp only [det2, splitComplement] at hD ⊢
  have hrecip : d * a - c * b ≠ 0 := by
    nlinarith
  field_simp [hD, hrecip]
  <;> ring

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

/-- In tuple coordinates `(a,b,c,d)`, this is the fixed quarter-turn
`(a,b,c,d) ↦ (c,d,-a,-b)`. -/
def splitQuarterTurn (A : M2) : M2 :=
  (A.2.2.1, A.2.2.2, -A.1, -A.2.1)

theorem splitQuarterTurn_sq (A : M2) :
    splitQuarterTurn (splitQuarterTurn A) = (-A.1,-A.2.1,-A.2.2.1,-A.2.2.2) := by
  rcases A with ⟨a,b,c,d⟩
  rfl

/-- The existing Grassmannian `tau` factors through the split-signature Hodge complement. -/
theorem tau_eq_splitQuarterTurn_splitComplement (A : M2) :
    tau A = splitQuarterTurn (splitComplement A) := by
  rcases A with ⟨a,b,c,d⟩
  rfl

end GppSplitSignatureHodgeGrassmannian
