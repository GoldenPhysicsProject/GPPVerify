import Mathlib.Tactic
import GppVerify.GrassmannianMass

/-!
# Grassmannian googly decomposition

This file isolates an exact finite-dimensional fact behind the current googly attack.
On the big cell represented by `[I|A]`, the Hodge/complement operation on Plucker
coordinates induces the chart map

  C(A) = -A^{-T}.

The existing Grassmannian map

  tau(A) = A epsilon / det(A)

is not literally `C`.  In 2x2 coordinates it factors as

  tau = R o C,

where `R = [[0,-1],[1,0]]` acts by a fixed quarter-turn on the chart matrix and
satisfies `R^2 = -I`.  Moreover `R` and `C` commute.  Therefore

  tau^2 = R^2 C^2 = -I.

This cleanly separates the involutive complementary-plane operation, which is the
candidate googly geometry, from the order-four lift carried by the fixed quarter-turn.
No identification of `R` with physical spin is made here.
-/

namespace GppGrassmannianGooglyDecomposition

/-- Four coordinates of a 2x2 matrix [[a,b],[c,d]]. -/
abbrev M2 := ℝ × ℝ × ℝ × ℝ

def det2 (A : M2) : ℝ := A.1 * A.2.2.2 - A.2.1 * A.2.2.1

/-- Complementary-plane chart map `C(A)=-A^{-T}`. -/
noncomputable def complement (A : M2) : M2 :=
  let D := det2 A
  (-A.2.2.2 / D, A.2.2.1 / D, A.2.1 / D, -A.1 / D)

/-- Fixed quarter-turn `R A`, for R=[[0,-1],[1,0]]. -/
def quarterTurn (A : M2) : M2 :=
  (-A.2.1, -A.2.2.2, A.1, A.2.2.1)

/-- Existing Grassmannian chart map in tuple form. -/
noncomputable def tau (A : M2) : M2 :=
  let D := det2 A
  (-A.2.1 / D, A.1 / D, -A.2.2.2 / D, A.2.2.1 / D)

/-- The quarter-turn squares to the central sign. -/
theorem quarterTurn_sq (A : M2) : quarterTurn (quarterTurn A) = (-A.1,-A.2.1,-A.2.2.1,-A.2.2.2) := by
  rcases A with ⟨a,b,c,d⟩
  rfl

/-- Hence the quarter-turn has order four. -/
theorem quarterTurn_four (A : M2) :
    quarterTurn (quarterTurn (quarterTurn (quarterTurn A))) = A := by
  rcases A with ⟨a,b,c,d⟩
  rfl

/-- The determinant of the complementary chart is reciprocal. -/
theorem det2_complement (A : M2) (hD : det2 A ≠ 0) :
    det2 (complement A) = 1 / det2 A := by
  rcases A with ⟨a,b,c,d⟩
  simp only [det2, complement] at hD ⊢
  field_simp [hD]
  ring

/-- Complementing twice returns the original chart. -/
theorem complement_involutive (A : M2) (hD : det2 A ≠ 0) :
    complement (complement A) = A := by
  rcases A with ⟨a,b,c,d⟩
  simp only [det2, complement] at hD ⊢
  have hrecip : d * a - c * b ≠ 0 := by
    nlinarith
  field_simp [hD, hrecip]
  <;> ring

/-- The complement and fixed quarter-turn commute. -/
theorem complement_quarterTurn_commute (A : M2) (hD : det2 A ≠ 0) :
    complement (quarterTurn A) = quarterTurn (complement A) := by
  rcases A with ⟨a,b,c,d⟩
  simp only [det2, complement, quarterTurn] at hD ⊢
  field_simp [hD]
  <;> ring

/-- Main factorization: the existing Grassmannian tau is quarter-turn after complement. -/
theorem tau_eq_quarterTurn_complement (A : M2) :
    tau A = quarterTurn (complement A) := by
  rcases A with ⟨a,b,c,d⟩
  rfl

/-- The factorization explains the nonlinear order-four law: tau squared is -identity. -/
theorem tau_sq_from_complement (A : M2) (hD : det2 A ≠ 0) :
    tau (tau A) = (-A.1,-A.2.1,-A.2.2.1,-A.2.2.2) := by
  rw [tau_eq_quarterTurn_complement, tau_eq_quarterTurn_complement]
  rw [complement_quarterTurn_commute (complement A)]
  · rw [complement_involutive A hD]
    exact quarterTurn_sq A
  · rw [det2_complement A hD]
    exact one_div_ne_zero hD

/-! ## Plucker-coordinate form of the complementary-plane map -/

structure P6 where
  p01 : ℝ
  p02 : ℝ
  p03 : ℝ
  p12 : ℝ
  p13 : ℝ
  p23 : ℝ
  deriving Repr

/-- Euclidean Hodge star in the ordered Plucker basis
`(01,02,03,12,13,23)`. -/
def pluckerStar (p : P6) : P6 :=
  ⟨p.p23, -p.p13, p.p12, p.p03, -p.p02, p.p01⟩

theorem pluckerStar_sq (p : P6) : pluckerStar (pluckerStar p) = p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rfl

/-- Klein-quadric polynomial. Its zero locus is the decomposable Plucker quadric. -/
def kleinQ (p : P6) : ℝ := p.p01*p.p23 - p.p02*p.p13 + p.p03*p.p12

/-- Hodge complement preserves the Klein quadric exactly. -/
theorem kleinQ_pluckerStar (p : P6) : kleinQ (pluckerStar p) = kleinQ p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [kleinQ, pluckerStar]
  ring

/-- Plucker coordinates of the graph plane `[I|A]`. -/
def chartPlucker (A : M2) : P6 :=
  ⟨1, A.2.2.1, A.2.2.2, -A.1, -A.2.1, det2 A⟩

/-- Hodge star of a graph-plane Plucker vector is exactly the complementary graph
plane, projectively normalized by `1/det A`. -/
theorem chartPlucker_complement (A : M2) (hD : det2 A ≠ 0) :
    chartPlucker (complement A) =
      let D := det2 A
      ⟨1, (pluckerStar (chartPlucker A)).p02 / D,
          (pluckerStar (chartPlucker A)).p03 / D,
          (pluckerStar (chartPlucker A)).p12 / D,
          (pluckerStar (chartPlucker A)).p13 / D,
          (pluckerStar (chartPlucker A)).p23 / D⟩ := by
  rcases A with ⟨a,b,c,d⟩
  simp only [chartPlucker, complement, det2, pluckerStar]
  ext <;> simp
  · field_simp [hD]
    ring

end GppGrassmannianGooglyDecomposition
