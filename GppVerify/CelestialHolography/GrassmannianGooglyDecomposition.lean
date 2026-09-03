import Mathlib.Tactic
import GppVerify.GrassmannianMass

/-!
# Grassmannian googly decomposition

On the big cell represented by `[I|A]`, the Euclidean Hodge/complement operation
induces `C(A)=-A^{-T}`.  The chart map `tau` factors as a fixed quarter-turn after
this complement.  This Euclidean convention is kept separate from the split-signature
construction in `SplitSignatureHodgeGrassmannian`.
-/

namespace GppGrassmannianGooglyDecomposition

abbrev M2 := ℝ × ℝ × ℝ × ℝ

def det2 (A : M2) : ℝ := A.1 * A.2.2.2 - A.2.1 * A.2.2.1

noncomputable def complement (A : M2) : M2 :=
  let D := det2 A
  (-A.2.2.2 / D, A.2.2.1 / D, A.2.1 / D, -A.1 / D)

/-- Fixed Euclidean quarter-turn `Q(a,b,c,d)=(-c,-d,a,b)`. -/
def quarterTurn (A : M2) : M2 :=
  (-A.2.2.1, -A.2.2.2, A.1, A.2.1)

noncomputable def tau (A : M2) : M2 :=
  let D := det2 A
  (-A.2.1 / D, A.1 / D, -A.2.2.2 / D, A.2.2.1 / D)

theorem quarterTurn_sq (A : M2) :
    quarterTurn (quarterTurn A) = (-A.1,-A.2.1,-A.2.2.1,-A.2.2.2) := by
  rcases A with ⟨a,b,c,d⟩
  rfl

theorem quarterTurn_four (A : M2) :
    quarterTurn (quarterTurn (quarterTurn (quarterTurn A))) = A := by
  rcases A with ⟨a,b,c,d⟩
  simp [quarterTurn]

theorem det2_complement (A : M2) (hD : det2 A ≠ 0) :
    det2 (complement A) = 1 / det2 A := by
  rcases A with ⟨a,b,c,d⟩
  simp only [det2, complement] at hD ⊢
  field_simp [hD]
  ring

theorem complement_involutive (A : M2) (hD : det2 A ≠ 0) :
    complement (complement A) = A := by
  rcases A with ⟨a,b,c,d⟩
  simp only [det2, complement] at hD ⊢
  have hrecip : d * a - c * b ≠ 0 := by
    intro h
    apply hD
    calc
      a * d - b * c = d * a - c * b := by ring
      _ = 0 := h
  field_simp [hD, hrecip]
  <;> ring

theorem complement_quarterTurn_commute (A : M2) (hD : det2 A ≠ 0) :
    complement (quarterTurn A) = quarterTurn (complement A) := by
  rcases A with ⟨a,b,c,d⟩
  simp only [det2, complement, quarterTurn] at hD ⊢
  field_simp [hD]
  <;> ring

theorem tau_eq_quarterTurn_complement (A : M2) :
    tau A = quarterTurn (complement A) := by
  rcases A with ⟨a,b,c,d⟩
  rfl

theorem tau_sq_from_complement (A : M2) (hD : det2 A ≠ 0) :
    tau (tau A) = (-A.1,-A.2.1,-A.2.2.1,-A.2.2.2) := by
  rw [tau_eq_quarterTurn_complement, tau_eq_quarterTurn_complement]
  rw [complement_quarterTurn_commute (complement A)]
  · rw [complement_involutive A hD]
    exact quarterTurn_sq A
  · rw [det2_complement A hD]
    exact one_div_ne_zero hD

structure P6 where
  p01 : ℝ
  p02 : ℝ
  p03 : ℝ
  p12 : ℝ
  p13 : ℝ
  p23 : ℝ

def pluckerStar (p : P6) : P6 :=
  ⟨p.p23, -p.p13, p.p12, p.p03, -p.p02, p.p01⟩

theorem pluckerStar_sq (p : P6) : pluckerStar (pluckerStar p) = p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rfl

def kleinQ (p : P6) : ℝ := p.p01*p.p23 - p.p02*p.p13 + p.p03*p.p12

theorem kleinQ_pluckerStar (p : P6) : kleinQ (pluckerStar p) = kleinQ p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [kleinQ, pluckerStar]
  ring

def chartPlucker (A : M2) : P6 :=
  ⟨1, A.2.2.1, A.2.2.2, -A.1, -A.2.1, det2 A⟩

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
  congr 1 <;> field_simp [hD] <;> ring

end GppGrassmannianGooglyDecomposition
