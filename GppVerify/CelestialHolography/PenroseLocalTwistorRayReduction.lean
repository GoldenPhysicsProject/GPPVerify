import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import GppVerify.CelestialHolography.EinsteinNullRaySL2Geometry

/-!
# Penrose local-twistor transport reduces to the rank-two projective Sturm system

Penrose's local-twistor transport along a null ray has the schematic spinor form

  D omega = - i k . pi,
  D pi    = - i P(k,.) . omega,

where `D` is differentiation/parallel transport along the ray and `P` is Penrose's
Schouten-type curvature tensor in his curvature convention.

Restrict to the natural null-incidence line

  omega^A = f lambda^A,
  k^{AA'} = lambda^A lambdatilde^{A'},

with the null spinors parallel along an affine ray, and define the scalar

  g = lambdatilde^{A'} pi_{A'}.

The transport equations reduce to

  D f = - i g,
  D g = - i kappa f,

where `kappa` is the null contraction of the curvature coefficient.  Eliminating `g`
gives

  D^2 f = - kappa f.

Equivalently, after the constant fibre change `p := -i g`, the state `(f,p)` obeys the
real/projective first-order system

  D f = p,
  D p = -kappa f,

with the same `[[0,1],[-kappa,0]]` generator formalized in
`EinsteinNullRaySL2Geometry`.

This module formalizes only that exact algebraic reduction, using an abstract derivative
operator which is assumed to commute with constant complex scalar multiplication.  It does
not formalize spinor covariant derivatives or identify curvature sign conventions.

Important convention note: Penrose's 2015 paper writes
`P_ab = R g_ab/12 - R_ab/2`, while many modern conformal-geometry references define the
Schouten tensor with the opposite displayed sign (and may also use the opposite Riemann
sign).  Therefore `kappa` here is deliberately convention-neutral.  Comparison with the
modern almost-Einstein equation must translate curvature conventions first.
-/

namespace GppPenroseLocalTwistorRayReduction

open Complex

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Abstract differentiation/transport operator along one ray. -/
variable (D : V → V)

/-- Constant-complex-linearity hypothesis needed for the scalar reduction. -/
def ConstantComplexLinear : Prop :=
  ∀ (c : ℂ) (v : V), D (c • v) = c • D v

/-- Penrose's two scalar first-order equations imply the projective/Sturm second-order
equation. -/
theorem penrose_pair_implies_sturm
    (hD : ConstantComplexLinear D)
    (f g : V) (kappa : ℂ)
    (h1 : D f = (-I) • g)
    (h2 : D g = (-I * kappa) • f) :
    D (D f) = (-kappa) • f := by
  rw [h1, hD]
  rw [h2]
  simp [smul_smul]
  ring_nf

/-- Change of fibre coordinate from Penrose's contracted momentum `g` to
`p := -i g`. -/
def projectiveMomentum (g : V) : V := (-I) • g

/-- The first Penrose equation becomes `D f = p`. -/
theorem first_equation_is_projective_state
    (f g : V)
    (h1 : D f = (-I) • g) :
    D f = projectiveMomentum g := by
  exact h1

/-- Under constant complex linearity, the second Penrose equation becomes
`D p = -kappa f`. -/
theorem second_equation_is_projective_state
    (hD : ConstantComplexLinear D)
    (f g : V) (kappa : ℂ)
    (h2 : D g = (-I * kappa) • f) :
    D (projectiveMomentum g) = (-kappa) • f := by
  rw [projectiveMomentum, hD, h2]
  simp [smul_smul]
  ring_nf

/-- Exact two-component package: after `p=-i g`, Penrose's incidence-restricted local
transport is the standard rank-two projective system. -/
theorem penrose_pair_is_projective_system
    (hD : ConstantComplexLinear D)
    (f g : V) (kappa : ℂ)
    (h1 : D f = (-I) • g)
    (h2 : D g = (-I * kappa) • f) :
    D f = projectiveMomentum g ∧
    D (projectiveMomentum g) = (-kappa) • f := by
  exact ⟨first_equation_is_projective_state D f g h1,
    second_equation_is_projective_state D hD f g kappa h2⟩

/-- The scalar transport matrix in Penrose variables `(f,g)`. -/
def penroseRayMatrix (kappa : ℂ) : ℂ × ℂ × ℂ × ℂ :=
  (0, -I, -I*kappa, 0)

/-- Its square is `-kappa` times the identity.  This is the matrix-level factorization
of the second-order projective equation. -/
theorem penroseRayMatrix_sq (kappa : ℂ) :
    let M := penroseRayMatrix kappa
    (M.1*M.1 + M.2.1*M.2.2.1,
     M.1*M.2.1 + M.2.1*M.2.2.2,
     M.2.2.1*M.1 + M.2.2.2*M.2.2.1,
     M.2.2.1*M.2.1 + M.2.2.2*M.2.2.2)
      = (-kappa,0,0,-kappa) := by
  simp [penroseRayMatrix]
  ring

end GppPenroseLocalTwistorRayReduction
