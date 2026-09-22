import Mathlib.Tactic
import GppVerify.CelestialHolography.KleinNullInfinityBoundary
import GppVerify.CelestialHolography.FlatInfinityCelestialFactorization

/-!
# The celestial (2,2) screen as the null-infinity Klein quotient

Let `I=(0,0,0,0,0,1)` be the flat infinity point in the six-dimensional Klein module.
Its orthogonal hyperplane is `I^perp={p01=0}`.  Quotienting this hyperplane by the null
line spanned by `I` removes the `p23` coordinate.  The four remaining coordinates

  (p02,p03,p12,p13)

form a `2x2` matrix, and the induced Klein quadratic form is

  Q = -p02*p13 + p03*p12 = -det [[p02,p03],[p12,p13]].

Thus the screen `I^perp/<I>` is the standard split `(2,2)` matrix model.  Left and right
`SL(2,R)` multiplication preserve its determinant, giving the two chiral factors of the
split Lorentz/conformal screen directly in the project's coordinates.

This file proves the finite-dimensional quotient/screen algebra.  The group-theoretic
statement that the Levi factor of the null-line stabilizer in `SO(3,3)` is
`R^* x SO(2,2)` (up to finite quotients), and that `Spin(2,2)` is covered by
`SL(2,R) x SL(2,R)`, is standard external structure rather than encoded as a Lie-group
theorem here.
-/

namespace GppInfinityLeviScreenGeometry

open GppGrassmannianGooglyDecomposition
open GppKleinNullInfinityBoundary
open GppFlatInfinityCelestialFactorization

/-- Four screen coordinates left after imposing `p01=0` and quotienting the `p23`
infinity-line direction. -/
def screen (p : P6) : M2 := (p.p02,p.p03,p.p12,p.p13)

/-- The induced screen quadratic form. -/
def screenQ (A : M2) : ℝ := - det2 A

/-- On the infinity orthogonal hyperplane, the six-dimensional Klein norm is exactly the
split determinant form on the four-dimensional screen. -/
theorem kleinQ_on_infinity_hyperplane
    (p : P6) (hp : p.p01 = 0) :
    kleinQ p = screenQ (screen p) := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [kleinQ, screenQ, screen, det2] at hp ⊢
  rw [hp]
  ring

/-- Moving along the null line spanned by the infinity point changes only `p23`. -/
def shiftAlongInfinity (t : ℝ) (p : P6) : P6 :=
  ⟨p.p01,p.p02,p.p03,p.p12,p.p13,p.p23+t⟩

/-- The screen projection is insensitive to the quotient direction `<I>`. -/
theorem screen_shiftAlongInfinity (t : ℝ) (p : P6) :
    screen (shiftAlongInfinity t p) = screen p := by
  rfl

/-- On `I^perp`, shifting along `<I>` also leaves the Klein norm unchanged. -/
theorem kleinQ_shiftAlongInfinity
    (t : ℝ) (p : P6) (hp : p.p01 = 0) :
    kleinQ (shiftAlongInfinity t p) = kleinQ p := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  simp [shiftAlongInfinity, kleinQ] at hp ⊢
  rw [hp]
  ring

/-- Standard `2x2` matrix multiplication on the screen carrier. -/
def mul2 (A B : M2) : M2 :=
  (A.1*B.1 + A.2.1*B.2.2.1,
   A.1*B.2.1 + A.2.1*B.2.2.2,
   A.2.2.1*B.1 + A.2.2.2*B.2.2.1,
   A.2.2.1*B.2.1 + A.2.2.2*B.2.2.2)

/-- Determinant is multiplicative in the explicit `2x2` screen model. -/
theorem det2_mul2 (A B : M2) :
    det2 (mul2 A B) = det2 A * det2 B := by
  rcases A with ⟨a,b,c,d⟩
  rcases B with ⟨e,f,g,h⟩
  simp [mul2, det2]
  ring

/-- Independent left/right screen action. -/
def leftRightAct (L R X : M2) : M2 := mul2 (mul2 L X) R

/-- The left/right action scales the screen determinant by the two group determinants. -/
theorem det2_leftRightAct (L R X : M2) :
    det2 (leftRightAct L R X) = det2 L * det2 X * det2 R := by
  simp [leftRightAct, det2_mul2]
  ring

/-- Consequently determinant-one left and right factors preserve the split screen metric. -/
theorem sl2_left_right_preserves_screenQ
    (L R X : M2) (hL : det2 L = 1) (hR : det2 R = 1) :
    screenQ (leftRightAct L R X) = screenQ X := by
  simp [screenQ, det2_leftRightAct, hL, hR]

/-- The same independent determinant-one factors preserve the screen null cone. -/
theorem sl2_left_right_preserves_null
    (L R X : M2) (hL : det2 L = 1) (hR : det2 R = 1)
    (hX : det2 X = 0) :
    det2 (leftRightAct L R X) = 0 := by
  rw [det2_leftRightAct, hL, hR, hX]
  ring

/-- A rank-one celestial spinor outer product is a null screen vector. -/
theorem celestial_spinor_product_is_screen_null
    (lambda lambdatilde : Spinor2) :
    screenQ (nullMomentum lambda lambdatilde) = 0 := by
  rw [screenQ, nullMomentum_det_zero]
  ring

/-- Embed a screen representative into `I^perp` with arbitrary coordinate along the
quotient direction. -/
def screenLift (A : M2) (r : ℝ) : P6 :=
  ⟨0,A.1,A.2.1,A.2.2.1,A.2.2.2,r⟩

/-- Lifting then projecting recovers the same screen representative. -/
theorem screen_screenLift (A : M2) (r : ℝ) :
    screen (screenLift A r) = A := by
  rcases A with ⟨a,b,c,d⟩
  rfl

/-- The lift always lies in the infinity orthogonal hyperplane. -/
theorem screenLift_on_infinity_hyperplane (A : M2) (r : ℝ) :
    OnInfinityHyperplane (screenLift A r) := by
  rw [onInfinityHyperplane_iff_p01_zero]
  rfl

/-- The Klein norm of a lifted screen point is independent of the quotient coordinate. -/
theorem kleinQ_screenLift (A : M2) (r : ℝ) :
    kleinQ (screenLift A r) = screenQ A := by
  apply kleinQ_on_infinity_hyperplane
  rfl

end GppInfinityLeviScreenGeometry
