import Mathlib.Tactic
import GppVerify.CelestialHolography.FlatNullWeylFiberGeometry
import GppVerify.CelestialHolography.GrassmannianGooglyDecomposition

/-!
# SL(2) geometry of null-ray Einstein-scale transport

For an affinely parametrized null geodesic, the almost-Einstein equation contracts to a
scalar second-order equation of the form

  sigma'' + U sigma = 0,

where geometrically `U=P(k,k)` is the Schouten contraction along the ray.  Writing the
state as `(sigma,sigma')` gives the first-order generator

  A_U = [[0,1],[-U,0]],

which is trace-free.  Equivalently it preserves the standard alternating form

  omega((x,p),(y,q)) = x*q-p*y

infinitesimally.  Therefore the corresponding fundamental transport, whenever defined,
lies in `SL(2)` and preserves the Wronskian.

This module formalizes the exact finite-dimensional algebra behind that statement.  It
does not formalize an ODE existence theorem or the curved almost-Einstein equation.

The same `SL(2)` geometry already occurs in the flat celestial kernel: the rank-one Weyl
representative `w(x,p)=(-p,x)` has determinant one, preserves `omega`, and squares to the
central sign `-1`, hence has projective order two.  This should be distinguished from its
six-dimensional orthogonal-vector action, whose reflection determinant is `-1`.
-/

namespace GppEinsteinNullRaySL2Geometry

open GppFlatNullWeylFiberGeometry
open GppGrassmannianGooglyDecomposition

abbrev RayState := ℝ × ℝ

/-- Standard alternating/Wronskian form on a two-dimensional solution-state fibre. -/
def omega (u v : RayState) : ℝ := u.1*v.2-u.2*v.1

/-- Action of a `2x2` matrix encoded by the project's `M2` carrier. -/
def act2 (M : M2) (u : RayState) : RayState :=
  (M.1*u.1 + M.2.1*u.2,
   M.2.2.1*u.1 + M.2.2.2*u.2)

/-- A linear map scales the Wronskian by its determinant. -/
theorem omega_act2 (M : M2) (u v : RayState) :
    omega (act2 M u) (act2 M v) = det2 M * omega u v := by
  rcases M with ⟨a,b,c,d⟩
  rcases u with ⟨x,p⟩
  rcases v with ⟨y,q⟩
  simp [omega, act2, det2]
  ring

/-- Hence every determinant-one matrix preserves the Wronskian exactly. -/
theorem omega_preserved_of_det_one
    (M : M2) (hM : det2 M = 1) (u v : RayState) :
    omega (act2 M u) (act2 M v) = omega u v := by
  rw [omega_act2, hM]
  ring

/-- First-order generator associated with `sigma''+U sigma=0`. -/
def einsteinRayGenerator (U : ℝ) : M2 := (0,1,-U,0)

/-- The Einstein null-ray generator has zero trace. -/
theorem einsteinRayGenerator_trace_zero (U : ℝ) :
    (einsteinRayGenerator U).1 + (einsteinRayGenerator U).2.2.2 = 0 := by
  simp [einsteinRayGenerator]

/-- Infinitesimal symplectic condition: the Einstein-ray generator lies in `sp(2,R)=sl(2,R)`. -/
theorem einsteinRayGenerator_infinitesimal_symplectic
    (U : ℝ) (u v : RayState) :
    omega (act2 (einsteinRayGenerator U) u) v +
      omega u (act2 (einsteinRayGenerator U) v) = 0 := by
  rcases u with ⟨x,p⟩
  rcases v with ⟨y,q⟩
  simp [omega, act2, einsteinRayGenerator]
  ring

/-- Standard Weyl representative on the rank-two state fibre. -/
def rayWeyl : M2 := (0,-1,1,0)

/-- The spinor/solution-fibre Weyl representative has determinant `+1`. -/
theorem rayWeyl_det_one : det2 rayWeyl = 1 := by
  norm_num [rayWeyl, det2]

/-- Its action agrees with the flat celestial Weyl spinor map already formalized. -/
theorem rayWeyl_action_eq_flatWeyl (u : RayState) :
    act2 rayWeyl u = weylSpinor u := by
  rcases u with ⟨x,p⟩
  rfl

/-- Consequently the Weyl representative preserves the Wronskian. -/
theorem rayWeyl_preserves_omega (u v : RayState) :
    omega (act2 rayWeyl u) (act2 rayWeyl v) = omega u v := by
  exact omega_preserved_of_det_one rayWeyl rayWeyl_det_one u v

/-- The Weyl representative squares to the central sign on the state fibre. -/
theorem rayWeyl_sq_central_sign (u : RayState) :
    act2 rayWeyl (act2 rayWeyl u) = scaleSpinor (-1) u := by
  rw [rayWeyl_action_eq_flatWeyl, rayWeyl_action_eq_flatWeyl]
  exact weylSpinor_sq u

/-- Lower-unipotent translation matrix, matching the flat affine kernel orbit. -/
def rayUnipotent (a : ℝ) : M2 := (1,0,a,1)

/-- The unipotent subgroup also lies in `SL(2)`. -/
theorem rayUnipotent_det_one (a : ℝ) : det2 (rayUnipotent a) = 1 := by
  norm_num [rayUnipotent, det2]

/-- Its matrix action is exactly the previously defined affine unipotent spinor action. -/
theorem rayUnipotent_action (a : ℝ) (u : RayState) :
    act2 (rayUnipotent a) u = unipotentSpinor a u := by
  rcases u with ⟨x,p⟩
  simp [act2, rayUnipotent, unipotentSpinor]

/-- Thus the same determinant-one geometry contains both the null-ray transport generator
and the Weyl/unipotent data underlying the flat principal-series intertwiner. -/
theorem weyl_and_unipotent_preserve_omega (a : ℝ) (u v : RayState) :
    omega (act2 rayWeyl u) (act2 rayWeyl v) = omega u v ∧
    omega (act2 (rayUnipotent a) u) (act2 (rayUnipotent a) v) = omega u v := by
  exact ⟨rayWeyl_preserves_omega u v,
    omega_preserved_of_det_one (rayUnipotent a) (rayUnipotent_det_one a) u v⟩

end GppEinsteinNullRaySL2Geometry
