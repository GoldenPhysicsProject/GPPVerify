import Mathlib.Tactic
import GppVerify.CelestialHolography.GrassmannianGooglyDecomposition
import GppVerify.CelestialHolography.SpinProductCenterTimeOrientation

/-!
# Relative spin-center orientation on the Gr(2,4) big cell

Write a big-cell point as a graph `[I|A]`, with `A` a 2x2 matrix carrying one left and
one right spinor index.  Independent central signs on the two spinor factors act on this
mixed object through their PRODUCT.  For the nontrivial relative-center coset this gives

  A -> -A.

Thus the same quotient sign that sends a factorized vector momentum `p -> -p` appears on
the Grassmannian spacetime chart as central inversion of the mixed spinor coordinate.

The quadratic determinant is even,

  det(-A)=det(A),

while both complement duality and the project's order-four `tau` map are odd/equivariant:

  C(-A)   = -C(A),
  tau(-A) = -tau(A).

So the relative orientation sign is compatible with the established Gr(2,4) duality
rather than being a separate ad hoc label.  The Lorentzian interpretation of `A->-A` as
simultaneous reversal of an oriented spacetime vector (and hence future/past on a timelike
ray) requires the usual real/soldering structure and is external to this real-coordinate
big-cell theorem.
-/

namespace GppGrassmannianRelativeCenterOrientation

open GppGrassmannianGooglyDecomposition
open GppSpinProductCenterTimeOrientation

/-- Coordinate negation on the big-cell matrix. -/
def negM2 (A : M2) : M2 := (-A.1,-A.2.1,-A.2.2.1,-A.2.2.2)

/-- The relative center acts on a mixed left-right matrix by the product character. -/
def centerActM2 (sL sR : ℝ) (A : M2) : M2 :=
  let t := vectorCenterCharacter sL sR
  (t*A.1,t*A.2.1,t*A.2.2.1,t*A.2.2.2)

/-- Diagonal center is invisible on the big-cell mixed-spinor coordinate. -/
theorem diagonal_center_M2_invisible (A : M2) :
    centerActM2 (-1) (-1) A = A := by
  rcases A with ⟨a,b,c,d⟩
  simp [centerActM2, vectorCenterCharacter]

/-- Either one-sided center flip is exactly `A -> -A`. -/
theorem relative_center_M2_is_negation (A : M2) :
    centerActM2 (-1) 1 A = negM2 A ∧
    centerActM2 1 (-1) A = negM2 A := by
  rcases A with ⟨a,b,c,d⟩
  constructor <;> simp [centerActM2, vectorCenterCharacter, negM2]

/-- The quadratic determinant/mass-shell interval is orientation-even. -/
theorem det2_negM2 (A : M2) : det2 (negM2 A) = det2 A := by
  rcases A with ⟨a,b,c,d⟩
  simp [det2, negM2]
  ring

/-- Complement/annihilator duality is equivariant with the relative orientation sign. -/
theorem complement_negM2 (A : M2) :
    complement (negM2 A) = negM2 (complement A) := by
  rcases A with ⟨a,b,c,d⟩
  simp [complement, negM2, det2]
  constructor
  · ring
  · constructor
    · ring
    · constructor <;> ring

/-- The order-four Grassmannian tau map is likewise odd under central inversion. -/
theorem tau_negM2 (A : M2) : tau (negM2 A) = negM2 (tau A) := by
  rcases A with ⟨a,b,c,d⟩
  simp [tau, negM2, det2]
  constructor
  · ring
  · constructor
    · ring
    · constructor <;> ring

/-- Quarter-turn is linear/odd as expected. -/
theorem quarterTurn_negM2 (A : M2) :
    quarterTurn (negM2 A) = negM2 (quarterTurn A) := by
  rcases A with ⟨a,b,c,d⟩
  rfl

/-- The orientation sign and the googly/complement involution commute on the big cell. -/
theorem orientation_complement_commute (A : M2) :
    complement (negM2 A) = negM2 (complement A) :=
  complement_negM2 A

end GppGrassmannianRelativeCenterOrientation
