import Mathlib.Tactic
import GppVerify.CelestialHolography.GrassmannianGooglyDecomposition
import GppVerify.CelestialHolography.TwistorAnnihilatorIncidence

/-!
# Klein-spinor incidence from the ambient four-form

Let `V` be an oriented real four-dimensional vector space.  The volume form does not
canonically identify `V` with `V*`, but it does canonically define the six-dimensional
Klein bilinear form on `Λ²V`.  In split signature this is the vector representation of
`Spin(3,3) ≅ SL(4,R)`, while the two four-dimensional half-spinor representations are
`V` and `V*`.

At the coordinate level used throughout this project, a Plucker bivector `p` therefore
acts between the two chiral twistor modules by the epsilon/contraction maps

  cPlus(p)  : V  -> V*
  cMinus(p) : V* -> V.

Their compositions are `-Q_Klein(p)` times the identity.  Hence on the Klein quadric
`Q_Klein(p)=0` the combined Clifford action is nilpotent rather than invertible.

For a graph point `p = chartPlucker(A)` the kernels are exactly the twistor line `W`
and its annihilator line `W^0`; the images contain the opposite incidence line.  Thus
one spacetime/Klein point intrinsically couples ordinary and dual twistor incidence
without any extra pointwise identification `V* ≅ V`.

This is finite-dimensional coordinate algebra only.  It does not formalize the Lie-group
isomorphism `Spin(3,3) ≅ SL(4,R)` itself or a projective Penrose transform.
-/

namespace GppKleinSpinorIncidence

open GppGrassmannianGooglyDecomposition
open GppTwistorAnnihilatorIncidence

/-- Coordinate scaling on the four-dimensional twistor module. -/
def scale4 (λ : ℝ) (x : V4) : V4 :=
  (λ*x.1, λ*x.2.1, λ*x.2.2.1, λ*x.2.2.2)

/-- Epsilon-induced action of a Klein bivector on an ordinary twistor, landing in the
dual twistor module.  Coordinates implement `w ↦ ε(p ∧ z ∧ w)`. -/
def cPlus (p : P6) (z : V4) : V4 :=
  (-p.p23*z.2.1 + p.p13*z.2.2.1 - p.p12*z.2.2.2,
   p.p23*z.1 - p.p03*z.2.2.1 + p.p02*z.2.2.2,
   -p.p13*z.1 + p.p03*z.2.1 - p.p01*z.2.2.2,
   p.p12*z.1 - p.p02*z.2.1 + p.p01*z.2.2.1)

/-- Contraction action of the same Klein bivector on a dual twistor, landing in the
ordinary twistor module.  With the displayed sign convention this is the standard
interior product of a covector with a bivector. -/
def cMinus (p : P6) (α : V4) : V4 :=
  (-p.p01*α.2.1 - p.p02*α.2.2.1 - p.p03*α.2.2.2,
   p.p01*α.1 - p.p12*α.2.2.1 - p.p13*α.2.2.2,
   p.p02*α.1 + p.p12*α.2.1 - p.p23*α.2.2.2,
   p.p03*α.1 + p.p13*α.2.1 + p.p23*α.2.2.1)

/-- Clifford relation on the ordinary-twistor chirality. -/
theorem cMinus_cPlus (p : P6) (z : V4) :
    cMinus p (cPlus p z) = scale4 (-kleinQ p) z := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases z with ⟨z0,z1,z2,z3⟩
  apply Prod.ext
  · simp [cMinus, cPlus, scale4, kleinQ]
    ring
  · apply Prod.ext
    · simp [cMinus, cPlus, scale4, kleinQ]
      ring
    · apply Prod.ext
      · simp [cMinus, cPlus, scale4, kleinQ]
        ring
      · simp [cMinus, cPlus, scale4, kleinQ]
        ring

/-- Clifford relation on the dual-twistor chirality. -/
theorem cPlus_cMinus (p : P6) (α : V4) :
    cPlus p (cMinus p α) = scale4 (-kleinQ p) α := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rcases α with ⟨a0,a1,a2,a3⟩
  apply Prod.ext
  · simp [cMinus, cPlus, scale4, kleinQ]
    ring
  · apply Prod.ext
    · simp [cMinus, cPlus, scale4, kleinQ]
      ring
    · apply Prod.ext
      · simp [cMinus, cPlus, scale4, kleinQ]
        ring
      · simp [cMinus, cPlus, scale4, kleinQ]
        ring

/-- Every graph-chart Plucker bivector is null for the Klein quadratic form. -/
theorem chartPlucker_klein_null (A : M2) :
    kleinQ (chartPlucker A) = 0 := by
  rcases A with ⟨a,b,c,d⟩
  simp [kleinQ, chartPlucker, det2]
  ring

/-- Therefore the epsilon Clifford action squares to zero on the ordinary-twistor
chirality at every spacetime/Klein point. -/
theorem chart_cMinus_cPlus_nilpotent (A : M2) (z : V4) :
    cMinus (chartPlucker A) (cPlus (chartPlucker A) z) = (0,0,0,0) := by
  rw [cMinus_cPlus, chartPlucker_klein_null]
  rcases z with ⟨z0,z1,z2,z3⟩
  simp [scale4]

/-- And likewise on the dual-twistor chirality. -/
theorem chart_cPlus_cMinus_nilpotent (A : M2) (α : V4) :
    cPlus (chartPlucker A) (cMinus (chartPlucker A) α) = (0,0,0,0) := by
  rw [cPlus_cMinus, chartPlucker_klein_null]
  rcases α with ⟨a0,a1,a2,a3⟩
  simp [scale4]

/-- A general point of the graph twistor line `W`. -/
def graphVector (a b c d r s : ℝ) : V4 :=
  (r,s,a*r+c*s,b*r+d*s)

/-- A general point of the annihilator dual-twistor line `W^0`. -/
def annihilatorVector (a b c d t u : ℝ) : V4 :=
  (-a*t-b*u,-c*t-d*u,t,u)

/-- The epsilon action kills the entire twistor line represented by the spacetime point. -/
theorem cPlus_kills_graph_line (a b c d r s : ℝ) :
    cPlus (chartPlucker (a,b,c,d)) (graphVector a b c d r s) = (0,0,0,0) := by
  simp [cPlus, chartPlucker, det2, graphVector]
  apply Prod.ext
  · ring
  · apply Prod.ext
    · ring
    · apply Prod.ext <;> ring

/-- The contraction action kills the entire annihilator dual-twistor line. -/
theorem cMinus_kills_annihilator_line (a b c d t u : ℝ) :
    cMinus (chartPlucker (a,b,c,d)) (annihilatorVector a b c d t u) = (0,0,0,0) := by
  simp [cMinus, chartPlucker, det2, annihilatorVector]
  apply Prod.ext
  · ring
  · apply Prod.ext
    · ring
    · apply Prod.ext <;> ring

/-- Exact kernel statement: at a graph-chart spacetime point, the kernel of `cPlus` is
precisely the corresponding ordinary twistor line. -/
theorem cPlus_kernel_is_graph_line (a b c d : ℝ) (z : V4) :
    cPlus (chartPlucker (a,b,c,d)) z = (0,0,0,0) ↔
      z = graphVector a b c d z.1 z.2.1 := by
  constructor
  · intro h
    rcases z with ⟨z0,z1,z2,z3⟩
    have h2 := congrArg (fun x : V4 => x.2.2.1) h
    have h3 := congrArg (fun x : V4 => x.2.2.2) h
    simp [cPlus, chartPlucker, det2] at h2 h3
    have hz2 : z2 = a*z0 + c*z1 := by linarith
    have hz3 : z3 = b*z0 + d*z1 := by linarith
    simp [graphVector, hz2, hz3]
  · intro h
    rw [h]
    exact cPlus_kills_graph_line a b c d _ _

/-- Exact kernel statement on the opposite chirality: the kernel of `cMinus` is exactly
the annihilator dual-twistor line. -/
theorem cMinus_kernel_is_annihilator_line (a b c d : ℝ) (α : V4) :
    cMinus (chartPlucker (a,b,c,d)) α = (0,0,0,0) ↔
      α = annihilatorVector a b c d α.2.2.1 α.2.2.2 := by
  constructor
  · intro h
    rcases α with ⟨a0,a1,a2,a3⟩
    have h0 := congrArg (fun x : V4 => x.1) h
    have h1 := congrArg (fun x : V4 => x.2.1) h
    simp [cMinus, chartPlucker, det2] at h0 h1
    have ha0 : a0 = -a*a2 - b*a3 := by linarith
    have ha1 : a1 = -c*a2 - d*a3 := by linarith
    simp [annihilatorVector, ha0, ha1]
  · intro h
    rw [h]
    exact cMinus_kills_annihilator_line a b c d _ _

/-- A simple dual basis vector maps directly to one graph-line generator. -/
theorem cMinus_dual_basis0_is_graphRow2 (a b c d : ℝ) :
    cMinus (chartPlucker (a,b,c,d)) (1,0,0,0) = graphRow2 c d := by
  simp [cMinus, chartPlucker, det2, graphRow2]

/-- The second dual basis vector maps to minus the other graph-line generator. -/
theorem cMinus_dual_basis1_is_minus_graphRow1 (a b c d : ℝ) :
    cMinus (chartPlucker (a,b,c,d)) (0,1,0,0) = (-1,0,-a,-b) := by
  simp [cMinus, chartPlucker, det2]

/-- An ordinary basis vector maps directly to one annihilator generator. -/
theorem cPlus_basis2_is_annihilator2 (a b c d : ℝ) :
    cPlus (chartPlucker (a,b,c,d)) (0,0,1,0) = annihilator2 b d := by
  simp [cPlus, chartPlucker, det2, annihilator2]

/-- The fourth ordinary basis vector maps to minus the other annihilator generator. -/
theorem cPlus_basis3_is_minus_annihilator1 (a b c d : ℝ) :
    cPlus (chartPlucker (a,b,c,d)) (0,0,0,1) = (a,c,-1,0) := by
  simp [cPlus, chartPlucker, det2]

/-- The direct sum of the two chiral twistor modules. -/
abbrev DiracTwistor := V4 × V4

/-- Full odd Clifford action: a Klein vector exchanges the two chiral half-spinor modules. -/
def cliffordAction (p : P6) (ψ : DiracTwistor) : DiracTwistor :=
  (cMinus p ψ.2, cPlus p ψ.1)

/-- Full Clifford square on the direct sum. -/
theorem cliffordAction_sq (p : P6) (ψ : DiracTwistor) :
    cliffordAction p (cliffordAction p ψ) =
      (scale4 (-kleinQ p) ψ.1, scale4 (-kleinQ p) ψ.2) := by
  rcases ψ with ⟨z,α⟩
  simp [cliffordAction, cMinus_cPlus, cPlus_cMinus]

/-- At every Klein-quadric spacetime point the full chiral-exchange Clifford operator is
nilpotent of order two. -/
theorem chart_cliffordAction_sq_zero (A : M2) (ψ : DiracTwistor) :
    cliffordAction (chartPlucker A) (cliffordAction (chartPlucker A) ψ) =
      ((0,0,0,0),(0,0,0,0)) := by
  rw [cliffordAction_sq, chartPlucker_klein_null]
  rcases ψ with ⟨z,α⟩
  rcases z with ⟨z0,z1,z2,z3⟩
  rcases α with ⟨a0,a1,a2,a3⟩
  simp [scale4]

end GppKleinSpinorIncidence
