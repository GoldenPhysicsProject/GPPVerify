import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import GppVerify.CelestialHolography.PenroseLocalTwistorEinsteinQuotient

/-!
# Homogeneity of the raywise Penrose--Einstein quotient

For a fixed null tangent

  k^{AA'} = lambda^A lambdatilde^{A'},

the spinor factorization has the usual little-group freedom

  lambda -> a lambda,
  lambdatilde -> a^{-1} lambdatilde,

with `a != 0` and `k` unchanged.

If the aligned primary local-twistor spinor is `omega=x lambda`, then the coefficient
changes as `x -> a^{-1}x`.  Likewise the contracted momentum
`p=lambdatilde.pi` changes as `p -> a^{-1}p`.  Thus the two-component quotient state
has a common homogeneity `-1` in this ray-spinor frame.

This file formalizes the resulting finite algebra:

* the projective ratio of the two components is frame-independent;
* the Einstein-ray generator commutes with the common rescaling;
* the two-state Wronskian acquires weight `-2`.

The final statement is exactly the kind of twist/homogeneity which makes a projective or
line-bundle-valued object natural rather than a globally normalized scalar.  It is not, by
itself, an identification with Penrose's TN43 twisted googly form or with LeBrun's
holomorphic Einstein bundle.
-/

namespace GppPenroseRayQuotientHomogeneity

open Complex
open GppPenroseLocalTwistorEinsteinQuotient

/-- Common weight `-1` change of quotient coordinates under a ray-spinor rescaling. -/
def rayFrameRescale (a : ℂ) (u : EinsteinRayState) : EinsteinRayState :=
  ((1/a) * u.1, (1/a) * u.2)

/-- The induced Einstein-ray generator is equivariant under common ray-frame rescaling. -/
theorem einsteinGenerator_rayFrameRescale
    (a U : ℂ) (u : EinsteinRayState) :
    einsteinRayGenerator U (rayFrameRescale a u) =
      rayFrameRescale a (einsteinRayGenerator U u) := by
  rcases u with ⟨x,p⟩
  simp [einsteinRayGenerator, rayFrameRescale]
  constructor <;> ring

/-- Affine projective coordinate on the patch where the second component is nonzero. -/
def quotientProjectiveRatio (u : EinsteinRayState) : ℂ := u.1 / u.2

/-- The projective coordinate is independent of the nonzero ray-spinor frame rescaling. -/
theorem quotientProjectiveRatio_rescale
    (a : ℂ) (ha : a ≠ 0) (u : EinsteinRayState) (hu : u.2 ≠ 0) :
    quotientProjectiveRatio (rayFrameRescale a u) = quotientProjectiveRatio u := by
  rcases u with ⟨x,p⟩
  simp [quotientProjectiveRatio, rayFrameRescale] at hu ⊢
  field_simp [ha, hu]
  ring

/-- Determinant/Wronskian form on two quotient states. -/
def quotientWronskian (u v : EinsteinRayState) : ℂ :=
  u.1*v.2 - u.2*v.1

/-- The Wronskian carries twice the quotient-state homogeneity. -/
theorem quotientWronskian_rescale
    (a : ℂ) (u v : EinsteinRayState) :
    quotientWronskian (rayFrameRescale a u) (rayFrameRescale a v) =
      (1/a)^2 * quotientWronskian u v := by
  rcases u with ⟨x,p⟩
  rcases v with ⟨y,q⟩
  simp [quotientWronskian, rayFrameRescale]
  ring

/-- Common rescaling preserves the zero/nonzero projective state whenever the frame scale
is nonzero. -/
theorem rayFrameRescale_eq_zero_iff
    (a : ℂ) (ha : a ≠ 0) (u : EinsteinRayState) :
    rayFrameRescale a u = (0,0) ↔ u = (0,0) := by
  rcases u with ⟨x,p⟩
  constructor
  · intro h
    have hx := congrArg Prod.fst h
    have hp := congrArg Prod.snd h
    simp [rayFrameRescale] at hx hp
    have hia : (1/a : ℂ) ≠ 0 := by simp [ha]
    have : x = 0 := by exact (mul_eq_zero.mp hx).resolve_left hia
    have : p = 0 := by exact (mul_eq_zero.mp hp).resolve_left hia
    simp [*]
  · intro h
    subst u
    simp [rayFrameRescale]

end GppPenroseRayQuotientHomogeneity
