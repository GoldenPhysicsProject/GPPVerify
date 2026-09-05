import Mathlib.Tactic
import GppVerify.CelestialHolography.KleinPinReflectionDegeneration

/-!
# Cosmological Klein reflection as a scaled Weyl conjugate

On the active hyperbolic `(p01,p23)` plane, the infinity-twistor reflection is

  R_Lambda(x,y) = (-Lambda*y, -x/Lambda).

For a positive-square parameter `Lambda=t^2` with `t != 0`, this is conjugate to the
fixed Weyl reflection

  w(x,y)=(-y,-x)

by the split torus dilation

  a_t(x,y)=(t*x,y/t).

Thus

  R_{t^2} = a_t o w o a_t^{-1}.

This finite-dimensional identity explains why all non-null positive-norm members of the
cosmological family represent the same Weyl reflection in different scale splittings.
The `t -> 0` limit leaves the group because `a_t^{-1}` diverges, matching the null
singularity of the pointwise reflection at flat infinity.

Representation-theoretically, normalized Knapp--Stein/light intertwiners implement the
corresponding Weyl reflection on principal-series fields.  That analytic identification
is external and is not formalized in this file.
-/

namespace GppKleinWeylReflectionConjugacy

abbrev Active2 := ℝ × ℝ

/-- Fixed order-two Weyl reflection on the hyperbolic plane. -/
def fixedWeyl (v : Active2) : Active2 := (-v.2,-v.1)

/-- Split-torus dilation. -/
def splitDilation (t : ℝ) (v : Active2) : Active2 := (t*v.1, v.2/t)

/-- Active block of the cosmological reflection. -/
def activeReflection (Lambda : ℝ) (v : Active2) : Active2 :=
  (-Lambda*v.2, -v.1/Lambda)

/-- The fixed Weyl element is involutive. -/
theorem fixedWeyl_sq (v : Active2) : fixedWeyl (fixedWeyl v) = v := by
  rcases v with ⟨x,y⟩
  rfl

/-- Nonzero split dilation is inverted by the reciprocal parameter. -/
theorem splitDilation_inverse
    (t : ℝ) (ht : t ≠ 0) (v : Active2) :
    splitDilation t (splitDilation (1/t) v) = v := by
  rcases v with ⟨x,y⟩
  apply Prod.ext <;> simp [splitDilation] <;> field_simp [ht] <;> ring

/-- Main conjugacy theorem: `R_{t^2}=a_t w a_t^{-1}`. -/
theorem activeReflection_sqParameter_eq_conjugatedWeyl
    (t : ℝ) (ht : t ≠ 0) (v : Active2) :
    activeReflection (t*t) v =
      splitDilation t (fixedWeyl (splitDilation (1/t) v)) := by
  rcases v with ⟨x,y⟩
  apply Prod.ext <;>
    simp [activeReflection, splitDilation, fixedWeyl] <;>
    field_simp [ht] <;> ring

/-- The active reflection itself is involutive for nonzero parameter. -/
theorem activeReflection_sq
    (Lambda : ℝ) (hLambda : Lambda ≠ 0) (v : Active2) :
    activeReflection Lambda (activeReflection Lambda v) = v := by
  rcases v with ⟨x,y⟩
  apply Prod.ext <;>
    simp [activeReflection] <;>
    field_simp [hLambda] <;> ring

/-- Its 2x2 determinant is `-1`, independently of the nonzero scale parameter. -/
theorem activeReflection_det
    (Lambda : ℝ) (hLambda : Lambda ≠ 0) :
    (0:ℝ)*0 - (-Lambda)*(-1/Lambda) = -1 := by
  field_simp [hLambda]

end GppKleinWeylReflectionConjugacy
