import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import GppVerify.CelestialHolography.PenroseLocalTwistorEinsteinQuotient

/-!
# Gauge covariance of the Penrose raywise Einstein quotient

The quotient

  E_gamma = T_gamma^aligned / <Z_gamma>

is only geometrically meaningful if it does not depend on arbitrary choices in an adapted
spin frame along the null ray.  This module proves the exact finite-dimensional covariance
under the two basic changes relevant to the adapted coordinate model.

1. Little-group rescaling of the null factorization

     lambda -> a lambda,
     lambdatilde -> a^{-1} lambdatilde,

   leaves k=lambda lambdatilde fixed.  For the quotient coordinates

     omega = x lambda,
     p = lambdatilde.pi,

   one gets `(x,p) -> a^{-1}(x,p)`.  Since `U=P(k,k)` is unchanged, the induced Einstein
   generator is equivariant under this common rescaling.

2. Change of complementary spinors in the adapted frame.  On the ray-aligned subspace
   such changes alter only coordinates discarded by the quotient (or add multiples of
   the aligned coordinate proportional to `y`, which vanishes there).  We model the most
   general triangular coordinate change needed for this statement and prove that the
   quotient projection is unchanged on aligned states.

This establishes that the two-dimensional system previously extracted from Penrose local
transport is projectively attached to the null ray rather than to one chosen spin-frame
normalization.  Global holomorphic gluing across different rays remains a separate problem.
-/

namespace GppPenroseLocalTwistorRayGaugeCovariance

open Complex
open GppPenroseLocalTwistorEinsteinQuotient

/-- Common scaling of the two quotient coordinates.  For a null-spinor little-group
rescaling by nonzero `a`, the quotient coordinates scale by `a^{-1}`. -/
def scaleEinsteinState (c : ℂ) (u : EinsteinRayState) : EinsteinRayState :=
  (c*u.1,c*u.2)

/-- The induced Einstein-ray generator commutes with common rescaling. -/
theorem einsteinRayGenerator_scale_equivariant
    (U c : ℂ) (u : EinsteinRayState) :
    einsteinRayGenerator U (scaleEinsteinState c u) =
      scaleEinsteinState c (einsteinRayGenerator U u) := by
  rcases u with ⟨x,p⟩
  simp [einsteinRayGenerator, scaleEinsteinState]
  constructor <;> ring

/-- Coordinate form of the quotient state under the little-group rescaling
`lambda -> a lambda`, `lambdatilde -> a^{-1} lambdatilde`. -/
def littleGroupState (a : ℂ) (ha : a ≠ 0) (u : EinsteinRayState) : EinsteinRayState :=
  scaleEinsteinState (a⁻¹) u

/-- Little-group covariance of the induced ray dynamics. -/
theorem littleGroup_generator_covariant
    (U a : ℂ) (ha : a ≠ 0) (u : EinsteinRayState) :
    einsteinRayGenerator U (littleGroupState a ha u) =
      littleGroupState a ha (einsteinRayGenerator U u) := by
  exact einsteinRayGenerator_scale_equivariant U (a⁻¹) u

/-- Two little-group gauge choices differ only by an overall nonzero projective scale on
`E_gamma`. -/
theorem littleGroup_state_is_projective_scale
    (a : ℂ) (ha : a ≠ 0) (u : EinsteinRayState) :
    ∃ c : ℂ, c ≠ 0 ∧ littleGroupState a ha u = scaleEinsteinState c u := by
  refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
  rfl

/-- Triangular change of complementary spin-frame coordinates.

`b` models `iota -> iota + b lambda`, which changes the coefficient `x` by a multiple of
`y`; `c` models the corresponding freedom in the complementary primed coordinate, which
changes only `q` by a multiple of `p`.  On `y=0`, both changes are invisible after quotient. -/
def complementChange (b c : ℂ) (Z : RayLocalTwistor) : RayLocalTwistor :=
  ⟨Z.x - b*Z.y, Z.y, Z.p, Z.q + c*Z.p⟩

/-- Complement changes preserve ray alignment. -/
theorem complementChange_preserves_alignment
    (b c : ℂ) (Z : RayLocalTwistor) (hZ : RayAligned Z) :
    RayAligned (complementChange b c Z) := by
  simpa [RayAligned, complementChange] using hZ

/-- On aligned local twistors, changing the complementary spinors does not alter the
quotient state. -/
theorem quotientProjection_complementChange
    (b c : ℂ) (Z : RayLocalTwistor) (hZ : RayAligned Z) :
    quotientProjection (complementChange b c Z) = quotientProjection Z := by
  rcases Z with ⟨x,y,p,q⟩
  simp [RayAligned] at hZ
  subst y
  simp [complementChange, quotientProjection]

/-- Therefore the projected Einstein dynamics is also independent of the complementary
spin-frame choice: both choices project to the same intrinsic generator value. -/
theorem projected_generator_complement_independent
    (U b c : ℂ) (Z : RayLocalTwistor) (hZ : RayAligned Z) :
    einsteinRayGenerator U (quotientProjection (complementChange b c Z)) =
      einsteinRayGenerator U (quotientProjection Z) := by
  rw [quotientProjection_complementChange b c Z hZ]

/-- The distinguished ray line remains invisible after any complement change. -/
theorem rayLine_complementChange_projects_zero
    (b c : ℂ) (Z : RayLocalTwistor) (hZ : InRayLine Z) :
    quotientProjection (complementChange b c Z) = (0,0) := by
  have hAlign : RayAligned Z := hZ.2.1
  rw [quotientProjection_complementChange b c Z hAlign]
  simp [quotientProjection, hZ.1, hZ.2.2]

/-- Gauge-covariant package: the quotient dynamics is equivariant under null-spinor
little-group rescaling and invariant under complementary-frame changes on the aligned
subspace. -/
theorem raywise_Einstein_quotient_gauge_package
    (U a b c : ℂ) (ha : a ≠ 0) (u : EinsteinRayState)
    (Z : RayLocalTwistor) (hZ : RayAligned Z) :
    einsteinRayGenerator U (littleGroupState a ha u) =
        littleGroupState a ha (einsteinRayGenerator U u) ∧
    quotientProjection (complementChange b c Z) = quotientProjection Z := by
  exact ⟨littleGroup_generator_covariant U a ha u,
    quotientProjection_complementChange b c Z hZ⟩

end GppPenroseLocalTwistorRayGaugeCovariance
