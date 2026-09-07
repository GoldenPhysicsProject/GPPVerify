import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

/-!
# Einstein ray system as a quotient of Penrose local-twistor transport

Penrose's local-twistor transport along a null ray with parallel spinor factorization

  k^{AA'} = lambda^A lambdatilde^{A'}

has the form

  D omega^B = -i lambda^B lambdatilde^{B'} pi_{B'},
  D pi_{B'} = -i lambda^A lambdatilde^{A'} P_{AA'BB'} omega^B.

Choose a parallel spin frame adapted to the ray.  Write the primary spinor as

  omega = x lambda + y iota

and write `p` for the contraction `lambdatilde.pi`; let `q` denote the complementary
primed component.  The transport generator has the coordinate form

  x' = -i p,
  y' = 0,
  p' = -i (U x + C y),
  q' = -i (D x + E y),

where `U = P(k,k)` and `C,D,E` are the remaining Schouten components in the adapted
frame.

The canonical ray-aligned subspace is `y=0`.  It is preserved by transport.  Inside it,
the one-dimensional line with `x=p=0` is the null-ray twistor itself; it is also preserved.
After quotienting by that ray line, the induced two-dimensional system is exactly

  x' = -i p,
  p' = -i U x,

hence `x'' + U x = 0`.  For `U=P(k,k)` this is the null contraction of the
almost-Einstein scale equation.

This file proves the complete finite-dimensional coordinate statement, including the
kernel/surjectivity algebra that identifies the quotient carrier with `C^2`.  The
spinorial derivation of the displayed adapted-frame transport equations from Penrose's
curved local-twistor connection is external differential geometry.
-/

namespace GppPenroseLocalTwistorEinsteinQuotient

open Complex

/-- Adapted components `(x,y,p,q)` of a local twistor along a null ray. -/
structure RayLocalTwistor where
  x : ℂ
  y : ℂ
  p : ℂ
  q : ℂ
  deriving Repr, DecidableEq

/-- Coordinate generator of Penrose local-twistor transport in a parallel ray-adapted
spin frame.  `U` is the null Schouten contraction `P(k,k)`; the other coefficients do
not survive the canonical quotient below. -/
def localTwistorGenerator (U C D E : ℂ) (Z : RayLocalTwistor) : RayLocalTwistor :=
  ⟨-I * Z.p,
   0,
   -I * (U * Z.x + C * Z.y),
   -I * (D * Z.x + E * Z.y)⟩

/-- Primary spinor aligned with the null-ray spinor line. -/
def RayAligned (Z : RayLocalTwistor) : Prop := Z.y = 0

/-- The distinguished one-dimensional ray-twistor line inside the aligned subspace. -/
def InRayLine (Z : RayLocalTwistor) : Prop :=
  Z.x = 0 ∧ Z.y = 0 ∧ Z.p = 0

/-- The aligned subspace is invariant under local-twistor transport. -/
theorem rayAligned_preserved
    (U C D E : ℂ) (Z : RayLocalTwistor) (hZ : RayAligned Z) :
    RayAligned (localTwistorGenerator U C D E Z) := by
  rfl

/-- The ray-twistor line is invariant; in fact the infinitesimal generator vanishes on it. -/
theorem rayLine_generator_zero
    (U C D E : ℂ) (Z : RayLocalTwistor) (hZ : InRayLine Z) :
    localTwistorGenerator U C D E Z = ⟨0,0,0,0⟩ := by
  rcases hZ with ⟨hx,hy,hp⟩
  apply RayLocalTwistor.ext <;> simp [localTwistorGenerator, hx, hy, hp]

abbrev EinsteinRayState := ℂ × ℂ

/-- Quotient coordinates: retain the aligned primary coefficient and the contraction of
`pi` with the ray spinor.  The complementary `q` direction is precisely the ray line. -/
def quotientProjection (Z : RayLocalTwistor) : EinsteinRayState := (Z.x,Z.p)

/-- Canonical lift of quotient coordinates to an aligned representative. -/
def quotientLift (u : EinsteinRayState) : RayLocalTwistor := ⟨u.1,0,u.2,0⟩

/-- The lift is aligned. -/
theorem quotientLift_aligned (u : EinsteinRayState) : RayAligned (quotientLift u) := by
  rfl

/-- Projection after the canonical lift is the identity. -/
theorem quotientProjection_lift (u : EinsteinRayState) :
    quotientProjection (quotientLift u) = u := by
  rcases u with ⟨x,p⟩
  rfl

/-- Thus every two-component Einstein-ray state has an aligned local-twistor representative. -/
theorem quotientProjection_surjective : Function.Surjective quotientProjection := by
  intro u
  exact ⟨quotientLift u, quotientProjection_lift u⟩

/-- On the aligned subspace, the kernel of the quotient projection is exactly the
one-dimensional ray-twistor line. -/
theorem aligned_projection_zero_iff_rayLine
    (Z : RayLocalTwistor) (hZ : RayAligned Z) :
    quotientProjection Z = (0,0) ↔ InRayLine Z := by
  constructor
  · intro h
    have hx : Z.x = 0 := congrArg Prod.fst h
    have hp : Z.p = 0 := congrArg Prod.snd h
    exact ⟨hx,hZ,hp⟩
  · rintro ⟨hx,hy,hp⟩
    simp [quotientProjection, hx, hp]

/-- Induced two-dimensional transport generator. -/
def einsteinRayGenerator (U : ℂ) (u : EinsteinRayState) : EinsteinRayState :=
  (-I * u.2, -I * U * u.1)

/-- Main quotient theorem: after imposing ray alignment, Penrose local-twistor transport
projects exactly to the two-dimensional Einstein-ray system, independent of the other
Schouten-frame coefficients and independent of the ray-line coordinate `q`. -/
theorem localTwistor_projects_to_EinsteinRay
    (U C D E : ℂ) (Z : RayLocalTwistor) (hZ : RayAligned Z) :
    quotientProjection (localTwistorGenerator U C D E Z) =
      einsteinRayGenerator U (quotientProjection Z) := by
  rcases Z with ⟨x,y,p,q⟩
  simp [RayAligned] at hZ
  subst y
  simp [quotientProjection, localTwistorGenerator, einsteinRayGenerator]
  ring

/-- Scalar multiplication on the two-dimensional quotient carrier. -/
def scaleState (a : ℂ) (u : EinsteinRayState) : EinsteinRayState :=
  (a*u.1,a*u.2)

/-- Applying the induced first-order generator twice gives `-U` times the identity.  In
ODE language this is precisely `x'' + U x = 0` (and likewise for the conjugate momentum
component). -/
theorem einsteinRayGenerator_sq (U : ℂ) (u : EinsteinRayState) :
    einsteinRayGenerator U (einsteinRayGenerator U u) = scaleState (-U) u := by
  rcases u with ⟨x,p⟩
  simp [einsteinRayGenerator, scaleState]
  constructor <;> ring_nf

/-- The quotient dynamics does not depend on which representative of an aligned state is
chosen along the invariant ray line: changing only `q` leaves both the quotient state and
its projected derivative unchanged. -/
def shiftRayLine (r : ℂ) (Z : RayLocalTwistor) : RayLocalTwistor :=
  ⟨Z.x,Z.y,Z.p,Z.q+r⟩

/-- Ray-line shifts are invisible in the quotient. -/
theorem quotientProjection_shiftRayLine (r : ℂ) (Z : RayLocalTwistor) :
    quotientProjection (shiftRayLine r Z) = quotientProjection Z := by
  rfl

/-- Projected transport is likewise independent of the representative along the ray line. -/
theorem projected_transport_shiftRayLine
    (U C D E r : ℂ) (Z : RayLocalTwistor) :
    quotientProjection (localTwistorGenerator U C D E (shiftRayLine r Z)) =
      quotientProjection (localTwistorGenerator U C D E Z) := by
  rfl

/-- Exact finite summary: the aligned local-twistor subspace modulo its invariant ray line
has carrier `C^2`, and its induced generator squares to `-U`. -/
theorem localTwistor_Einstein_quotient_package
    (U C D E : ℂ) :
    Function.Surjective quotientProjection ∧
    (∀ Z : RayLocalTwistor, RayAligned Z →
      (quotientProjection Z = (0,0) ↔ InRayLine Z)) ∧
    (∀ Z : RayLocalTwistor, RayAligned Z →
      quotientProjection (localTwistorGenerator U C D E Z) =
        einsteinRayGenerator U (quotientProjection Z)) ∧
    (∀ u : EinsteinRayState,
      einsteinRayGenerator U (einsteinRayGenerator U u) = scaleState (-U) u) := by
  refine ⟨quotientProjection_surjective, ?_, ?_, einsteinRayGenerator_sq U⟩
  · intro Z hZ
    exact aligned_projection_zero_iff_rayLine Z hZ
  · intro Z hZ
    exact localTwistor_projects_to_EinsteinRay U C D E Z hZ

end GppPenroseLocalTwistorEinsteinQuotient
