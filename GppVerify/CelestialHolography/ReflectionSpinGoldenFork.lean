import Mathlib.Tactic
import GppVerify.CelestialHolography.AmbitwistorGoldenPGL2Bridge
import GppVerify.StandardModel.NullRayDiracWeylBridge

/-!
# One reciprocal involution, two completions: spinorial Z4 and the golden hyperbolic word

The same reciprocal ray involution

    J(x,p) = (p,x)

now sits at a genuine structural fork.

## Elliptic/spin completion

Compose `J` with the independent coordinate reflection

    R(x,p)=(-x,p).

Both `R` and `J` reverse the Wronskian.  Their product is therefore symplectic:

    R J(x,p)=(-p,x)=w(x,p),

exactly the null-ray Weyl quarter-turn already proved to satisfy `w^2=-1`, `w^4=1` and to
intertwine with both the Grassmannian elliptic sector and the Dirac quarter-cycle.

## Hyperbolic/golden completion

Compose the *same* `J` instead with the primitive unipotent shear

    N_1(x,p)=(x,x+p).

This is `goldenRayStep = N_1 J`, whose projective action is `z -> 1+1/z`.  Its square is the
minimal trace-three hyperbolic sector and has the golden fixed/eigenvalue data.

So the order-four spinor structure and the golden hyperbolic structure are not unrelated
numerical coincidences: at the finite `PGL(2)` level they are two different completions of
the same reciprocal involution.

This theorem does NOT say Nature must choose either completion.  Physical selection still
requires the global bundle/integral-lattice and discrete-symmetry dictionaries.  It does
identify exactly where a future `phi` should be looked for: whenever the physical
reciprocity involution is completed by a canonical primitive unipotent rather than by the
second reflection that gives the spin lift.
-/

namespace GppReflectionSpinGoldenFork

open GppEinsteinNullRaySL2Geometry
open GppAmbitwistorGoldenPGL2Bridge
open GppNullRayDiracWeylBridge

/-- Independent coordinate reflection on the ray state. -/
def rayFirstReflection (u : RayState) : RayState := (-u.1,u.2)

/-- The coordinate reflection is involutive. -/
theorem rayFirstReflection_involution (u : RayState) :
    rayFirstReflection (rayFirstReflection u) = u := by
  rcases u with ⟨x,p⟩
  simp [rayFirstReflection]

/-- It reverses the Wronskian. -/
theorem rayFirstReflection_reverses_omega (u v : RayState) :
    omega (rayFirstReflection u) (rayFirstReflection v) = - omega u v := by
  rcases u with ⟨x,p⟩
  rcases v with ⟨y,q⟩
  simp [rayFirstReflection, omega]
  ring

/-- Product of the two anti-symplectic involutions is exactly the Weyl quarter-turn. -/
theorem two_reflections_eq_rayWeyl (u : RayState) :
    rayFirstReflection (act2 rayReciprocal u) = act2 rayWeyl u := by
  rcases u with ⟨x,p⟩
  simp [rayFirstReflection, act2, rayReciprocal, rayWeyl]

/-- Thus the elliptic completion of reciprocal exchange is the order-four Weyl lift. -/
theorem elliptic_completion_sq_is_central_sign (u : RayState) :
    rayFirstReflection
      (act2 rayReciprocal
        (rayFirstReflection (act2 rayReciprocal u))) =
      GppFlatNullWeylFiberGeometry.scaleSpinor (-1) u := by
  rw [two_reflections_eq_rayWeyl, two_reflections_eq_rayWeyl]
  exact rayWeyl_sq_central_sign u

/-- The hyperbolic completion uses the same reciprocal involution but the unit unipotent. -/
theorem hyperbolic_completion_is_goldenStep (u : RayState) :
    act2 (rayUnipotent 1) (act2 rayReciprocal u) = goldenRayStep u := by
  rfl

/-- On the positive affine chart its fixed point is therefore exactly the golden ratio. -/
theorem hyperbolic_completion_positive_fixed_iff_phi
    {z : ℝ} (hz : 0 < z) :
    z = 1 + 1/z ↔ z = Real.goldenRatio :=
  goldenRayStep_positive_fixed_iff_phi hz

/-- The same ray Weyl completion is transported exactly to the Dirac quarter-cycle. -/
theorem elliptic_completion_intertwines_dirac (u : RayState) :
    GppGrassmannianDiracIntertwiner.Uq *ᵥ rayToDirac u =
      rayToDirac (rayFirstReflection (act2 rayReciprocal u)) := by
  rw [two_reflections_eq_rayWeyl]
  exact Uq_rayToDirac u

end GppReflectionSpinGoldenFork
