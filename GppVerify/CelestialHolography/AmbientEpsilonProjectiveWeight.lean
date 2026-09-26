import Mathlib.Tactic
import GppVerify.CelestialHolography.TwistorCanonicalShift

/-!
# Ambient epsilon and the projective twistor weight four

The projective twistor three-form is obtained by contracting an ambient rank-four
alternating form with the Euler/radial vector. Algebraically it has one copy of the
homogeneous coordinate and three copies of its differential, so simultaneous projective
scaling contributes four powers of the scale.

This file formalizes that rank-four scaling statement without pretending to construct
the full differential-form geometry of CP^3. It is the exact algebraic source of the
`+4` top-form weight and hence the canonical degree `-4` used by the twistor Fourier
reflection `k -> -k-4`.
-/

namespace GppAmbientEpsilonProjectiveWeight

open GppTwistorCanonicalShift

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- An ambient rank-four covariant form, represented as a fully parenthesized curried
4-linear map so Lean can resolve every intermediate module instance. -/
abbrev FourForm :=
  V →ₗ[K] (V →ₗ[K] (V →ₗ[K] (V →ₗ[K] K)))

/-- Algebraic Euler contraction evaluated on three tangent directions. -/
def eulerContract (ε : FourForm (K:=K) (V:=V)) (Z d1 d2 d3 : V) : K :=
  ε Z d1 d2 d3

/-- Simultaneously scaling the homogeneous coordinate and its three differential
slots gives exactly four powers of the projective scale. -/
theorem eulerContract_scale_four
    (ε : FourForm (K:=K) (V:=V)) (c : K) (Z d1 d2 d3 : V) :
    eulerContract ε (c • Z) (c • d1) (c • d2) (c • d3) =
      c ^ 4 * eulerContract ε Z d1 d2 d3 := by
  simp [eulerContract]
  ring

/-- The number of homogeneous factors in the Euler-contracted ambient four-form is
exactly four. -/
theorem projective_top_weight_eq_four : (4 : ℤ) = -canonicalDegree := by
  norm_num [canonicalDegree, projectiveTwistorDim]

/-- Therefore the inverse line-bundle degree carried by the projective canonical
bundle is `-4`. -/
theorem canonical_degree_from_epsilon_rank_four : canonicalDegree = -4 := by
  norm_num [canonicalDegree, projectiveTwistorDim]

/-- Combining the ambient top-form weight with representation dualization gives the
canonical rank-four projective Fourier reflection. -/
theorem epsilon_forces_fourier_weight (k : ℤ) :
    canonicalDegree - k = -k - 4 := by
  rw [canonical_degree_from_epsilon_rank_four]
  omega

end GppAmbientEpsilonProjectiveWeight
