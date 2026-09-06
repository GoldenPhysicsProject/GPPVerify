import Mathlib.Tactic
import GppVerify.CelestialHolography.GrassmannianGooglyDecomposition

/-!
# Null-screen optical curvature: Ricci trace plus Weyl/shear part

For a null geodesic in four space-time dimensions, transverse geodesic deviation acts on
a two-dimensional screen.  Its optical tidal/Jacobi endomorphism therefore admits the
canonical algebraic decomposition

  R = (tr R / 2) I + W,

with `tr W = 0`.

Differential-geometric interpretation (external to this finite coordinate module):

* the trace part is the null Ricci focusing contribution and is the part removed by the
  Einstein/sky-projective condition `Ric(k,k)=0`;
* in vacuum, the surviving trace-free part is the projected Weyl tidal/shear curvature.

This is the exact finite-dimensional distinction suggested by Penrose's TN44 observation
that ordinary shear-free chiral propagation can discard genuine gravitational information:
vanishing Ricci trace does not force the transverse curvature operator itself to vanish.

For the GPP split `(2,2)` working slice, the null screen has signature `(1,1)`.  A screen
endomorphism self-adjoint with respect to `eta=diag(1,-1)` has matrix

  [[a,b],[-b,d]],

and its trace-free part therefore has exactly two real components

  [[u,v],[-v,-u]].

No identification of these two real components with global helicity sectors is made in
this file; that requires the four-dimensional Weyl/spinor geometry.
-/

namespace GppNullOpticalRicciWeylSplit

open GppGrassmannianGooglyDecomposition

/-- Trace of the explicit `2x2` carrier. -/
def trace2 (A : M2) : ℝ := A.1 + A.2.2.2

/-- Scalar matrix on the two-dimensional screen. -/
def scalar2 (r : ℝ) : M2 := (r,0,0,r)

/-- Coordinatewise addition. -/
def add2 (A B : M2) : M2 :=
  (A.1+B.1, A.2.1+B.2.1, A.2.2.1+B.2.2.1, A.2.2.2+B.2.2.2)

/-- Coordinatewise subtraction. -/
def sub2 (A B : M2) : M2 :=
  (A.1-B.1, A.2.1-B.2.1, A.2.2.1-B.2.2.1, A.2.2.2-B.2.2.2)

/-- Ricci/focusing scalar part of a two-dimensional optical curvature operator. -/
def tracePart (A : M2) : M2 := scalar2 (trace2 A / 2)

/-- Trace-free optical curvature part. -/
def traceFreePart (A : M2) : M2 := sub2 A (tracePart A)

/-- The trace-free part really has zero trace. -/
theorem trace_traceFreePart (A : M2) : trace2 (traceFreePart A) = 0 := by
  rcases A with ⟨a,b,c,d⟩
  simp [trace2, traceFreePart, tracePart, scalar2, sub2]
  ring

/-- Exact decomposition into scalar trace plus trace-free curvature. -/
theorem trace_decomposition (A : M2) :
    add2 (tracePart A) (traceFreePart A) = A := by
  rcases A with ⟨a,b,c,d⟩
  apply Prod.ext
  · simp [add2, tracePart, traceFreePart, scalar2, sub2, trace2]
    ring
  · apply Prod.ext
    · simp [add2, tracePart, traceFreePart, scalar2, sub2, trace2]
    · apply Prod.ext
      · simp [add2, tracePart, traceFreePart, scalar2, sub2, trace2]
      · simp [add2, tracePart, traceFreePart, scalar2, sub2, trace2]
        ring

/-- Vanishing trace-free part is exactly the condition that the screen curvature is a
scalar multiple of the identity. -/
theorem traceFreePart_eq_zero_iff_scalar (A : M2) :
    traceFreePart A = (0,0,0,0) ↔ A = tracePart A := by
  rcases A with ⟨a,b,c,d⟩
  simp [traceFreePart, tracePart, scalar2, sub2, trace2]
  constructor
  · rintro ⟨h1,h2,h3,h4⟩
    apply Prod.ext
    · exact sub_eq_zero.mp h1
    · apply Prod.ext
      · exact h2
      · apply Prod.ext
        · exact h3
        · exact sub_eq_zero.mp h4
  · intro h
    rcases h with rfl
    simp [sub2]

/-- Vacuum Ricci focusing (`trace=0`) does not imply vanishing optical curvature: a
nonzero trace-free operator remains possible. -/
theorem zero_trace_nonzero_example :
    trace2 (1,0,0,-1) = 0 ∧ (1,0,0,-1 : M2) ≠ (0,0,0,0) := by
  constructor
  · norm_num [trace2]
  · norm_num

/-- Split-screen bilinear form `eta=diag(1,-1)`. -/
def splitPair (x y : ℝ × ℝ) : ℝ := x.1*y.1 - x.2*y.2

/-- Action of the explicit screen matrix. -/
def actScreen (A : M2) (x : ℝ × ℝ) : ℝ × ℝ :=
  (A.1*x.1 + A.2.1*x.2,
   A.2.2.1*x.1 + A.2.2.2*x.2)

/-- Self-adjointness with respect to the split `(1,1)` screen metric. -/
def SplitSelfAdjoint (A : M2) : Prop :=
  ∀ x y : ℝ × ℝ, splitPair (actScreen A x) y = splitPair x (actScreen A y)

/-- Coordinate characterization of split self-adjoint screen operators. -/
theorem splitSelfAdjoint_iff_offdiag_opposite (A : M2) :
    SplitSelfAdjoint A ↔ A.2.2.1 = -A.2.1 := by
  rcases A with ⟨a,b,c,d⟩
  constructor
  · intro h
    have hxy := h (1,0) (0,1)
    simp [SplitSelfAdjoint, splitPair, actScreen] at hxy
    linarith
  · intro hc x y
    rcases x with ⟨x0,x1⟩
    rcases y with ⟨y0,y1⟩
    simp [SplitSelfAdjoint, splitPair, actScreen] at hc ⊢
    rw [hc]
    ring

/-- The trace-free part of a split-self-adjoint operator is again split-self-adjoint. -/
theorem traceFreePart_splitSelfAdjoint
    (A : M2) (hA : SplitSelfAdjoint A) :
    SplitSelfAdjoint (traceFreePart A) := by
  rw [splitSelfAdjoint_iff_offdiag_opposite] at hA ⊢
  rcases A with ⟨a,b,c,d⟩
  simp [traceFreePart, tracePart, scalar2, sub2, trace2] at hA ⊢
  exact hA

/-- Every split-self-adjoint trace-free operator has exactly two real components. -/
theorem splitSelfAdjoint_traceFree_normalForm
    (A : M2) (hSA : SplitSelfAdjoint A) (htr : trace2 A = 0) :
    A = (A.1, A.2.1, -A.2.1, -A.1) := by
  have hc := (splitSelfAdjoint_iff_offdiag_opposite A).mp hSA
  rcases A with ⟨a,b,c,d⟩
  simp [trace2] at htr
  simp at hc
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · simpa using hc
      · linarith

/-- Conversely every two-parameter normal form is split-self-adjoint and trace-free. -/
theorem two_component_form_is_splitSelfAdjoint_traceFree (u v : ℝ) :
    SplitSelfAdjoint (u,v,-v,-u) ∧ trace2 (u,v,-v,-u) = 0 := by
  constructor
  · rw [splitSelfAdjoint_iff_offdiag_opposite]
    simp
  · simp [trace2]

/-- The square of the trace-free split-self-adjoint two-component curvature is scalar. -/
theorem two_component_square (u v : ℝ) :
    let A : M2 := (u,v,-v,-u)
    (A.1*A.1 + A.2.1*A.2.2.1,
     A.1*A.2.1 + A.2.1*A.2.2.2,
     A.2.2.1*A.1 + A.2.2.2*A.2.2.1,
     A.2.2.1*A.2.1 + A.2.2.2*A.2.2.2) =
      scalar2 (u*u-v*v) := by
  simp [scalar2]
  ring

end GppNullOpticalRicciWeylSplit
