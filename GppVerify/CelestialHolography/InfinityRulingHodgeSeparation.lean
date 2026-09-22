import Mathlib.Tactic
import GppVerify.CelestialHolography.InfinityLeviScreenGeometry
import GppVerify.CelestialHolography.SplitSignatureHodgeGrassmannian

/-!
# Celestial ruling exchange is not the split Hodge star

At flat conformal infinity the null screen is the split `2 x 2` matrix model

    X = lambda tensor lambdatilde,

with the two projective spinors giving the two rulings of the celestial rank-one quadric.
There are two superficially similar but mathematically different operations:

1. **Ruling exchange** swaps the two spinor factors.  On the screen matrix this is
   ordinary transpose

       X -> X^T.

   It exchanges the left and right `SL(2)` actions and preserves the determinant/null cone.

2. The split-signature Hodge star on the ambient Klein bivector acts on the screen as
   the cofactor matrix

       [[a,b],[c,d]] -> [[d,-c],[-b,a]].

   On a rank-one spinor product this rotates each spinor separately by the epsilon
   quarter-turn `(u0,u1)->(u1,-u0)`; it does **not** swap the two ruling factors.

This distinction is important for the googly programme.  Exchanging the two celestial/
ambitwistor rulings and reversing the Hodge orientation of reconstructed spacetime
curvature may ultimately be intertwined by the curved reconstruction, but they are not
literally the same finite-dimensional map.  The theorem establishing that intertwiner
must therefore be proved rather than inserted by notation.
-/

namespace GppInfinityRulingHodgeSeparation

open GppGrassmannianGooglyDecomposition
open GppFlatInfinityCelestialFactorization
open GppInfinityLeviScreenGeometry
open GppSplitSignatureHodgeGrassmannian

/-- Matrix transpose on the split celestial screen. -/
def screenTranspose (A : M2) : M2 :=
  (A.1, A.2.2.1, A.2.1, A.2.2.2)

/-- The screen map induced by the ambient split Hodge star.  In row-major notation this is
`[[a,b],[c,d]] -> [[d,-c],[-b,a]]`. -/
def screenCofactor (A : M2) : M2 :=
  (A.2.2.2, -A.2.2.1, -A.2.1, A.1)

/-- Standard epsilon quarter-turn on a two-spinor. -/
def epsilonTurn2 (u : Spinor2) : Spinor2 := (u.2, -u.1)

/-- Ruling exchange is involutive. -/
theorem screenTranspose_involutive (A : M2) :
    screenTranspose (screenTranspose A) = A := by
  rcases A with ⟨a,b,c,d⟩
  rfl

/-- Ruling exchange preserves the determinant and hence the screen null cone. -/
theorem det2_screenTranspose (A : M2) :
    det2 (screenTranspose A) = det2 A := by
  rcases A with ⟨a,b,c,d⟩
  simp [screenTranspose, det2]
  ring

/-- The split-Hodge screen cofactor is also involutive. -/
theorem screenCofactor_involutive (A : M2) :
    screenCofactor (screenCofactor A) = A := by
  rcases A with ⟨a,b,c,d⟩
  rfl

/-- The split-Hodge screen cofactor preserves the determinant. -/
theorem det2_screenCofactor (A : M2) :
    det2 (screenCofactor A) = det2 A := by
  rcases A with ⟨a,b,c,d⟩
  simp [screenCofactor, det2]
  ring

/-- Exact ruling statement: transposing a rank-one celestial momentum swaps the two
spinor factors. -/
theorem screenTranspose_nullMomentum (lambda lambdatilde : Spinor2) :
    screenTranspose (nullMomentum lambda lambdatilde) =
      nullMomentum lambdatilde lambda := by
  rcases lambda with ⟨l0,l1⟩
  rcases lambdatilde with ⟨t0,t1⟩
  simp [screenTranspose, nullMomentum]
  constructor
  · ring
  · constructor
    · ring
    · constructor <;> ring

/-- Consequently the rank-one/null condition survives ruling exchange. -/
theorem rulingExchange_preserves_nullMomentum
    (lambda lambdatilde : Spinor2) :
    det2 (screenTranspose (nullMomentum lambda lambdatilde)) = 0 := by
  rw [det2_screenTranspose]
  exact nullMomentum_det_zero lambda lambdatilde

/-- Transpose exchanges the two independent screen group actions:
`(L X R)^T = R^T X^T L^T`. -/
theorem screenTranspose_swaps_left_right_actions
    (L R X : M2) :
    screenTranspose (leftRightAct L R X) =
      leftRightAct (screenTranspose R) (screenTranspose L) (screenTranspose X) := by
  rcases L with ⟨a,b,c,d⟩
  rcases R with ⟨e,f,g,h⟩
  rcases X with ⟨x,y,z,w⟩
  apply Prod.ext
  · simp [screenTranspose, leftRightAct, mul2]
    ring
  · apply Prod.ext
    · simp [screenTranspose, leftRightAct, mul2]
      ring
    · apply Prod.ext
      · simp [screenTranspose, leftRightAct, mul2]
        ring
      · simp [screenTranspose, leftRightAct, mul2]
        ring

/-- The ambient split Hodge star restricts on the four screen coordinates to the cofactor
map, not to ruling exchange/transpose. -/
theorem screen_splitStar_eq_screenCofactor (p : P6) :
    screen (splitStar p) = screenCofactor (screen p) := by
  rcases p with ⟨p01,p02,p03,p12,p13,p23⟩
  rfl

/-- On a rank-one celestial momentum the Hodge-induced screen map rotates each spinor by
the epsilon quarter-turn separately.  In particular it does not exchange their types. -/
theorem screenCofactor_nullMomentum
    (lambda lambdatilde : Spinor2) :
    screenCofactor (nullMomentum lambda lambdatilde) =
      nullMomentum (epsilonTurn2 lambda) (epsilonTurn2 lambdatilde) := by
  rcases lambda with ⟨l0,l1⟩
  rcases lambdatilde with ⟨t0,t1⟩
  simp [screenCofactor, nullMomentum, epsilonTurn2]
  constructor
  · ring
  · constructor
    · ring
    · constructor <;> ring

/-- Concrete separation witness: ruling exchange and the split-Hodge screen action are
not the same operation. -/
theorem screenTranspose_ne_screenCofactor :
    screenTranspose ((1,2,3,4) : M2) ≠ screenCofactor ((1,2,3,4) : M2) := by
  norm_num [screenTranspose, screenCofactor]

/-- Applying the actual ambient split Hodge star to a null screen lift therefore gives
factorwise epsilon rotation on the screen, while ruling exchange would give factor swap. -/
theorem splitStar_screen_of_nullLift
    (lambda lambdatilde : Spinor2) (r : ℝ) :
    screen (splitStar (screenLift (nullMomentum lambda lambdatilde) r)) =
      nullMomentum (epsilonTurn2 lambda) (epsilonTurn2 lambdatilde) := by
  rw [screen_splitStar_eq_screenCofactor, screen_screenLift,
      screenCofactor_nullMomentum]

end GppInfinityRulingHodgeSeparation
