import GppVerify.CelestialHolography.HolographicChain
import Mathlib.Tactic

/-!
# Antiunitary googly exchange on ∧²ℂ⁴

The Hodge-star decomposition in `HolographicChain` already gives explicit self-dual
and anti-self-dual sectors.  Complex conjugation alone preserves those sectors because
the chosen Hodge-star matrix is real.  The helicity/googly exchange therefore also
requires orientation reversal.  The map below combines complex conjugation with an
orientation sign flip and hence anti-commutes with the Hodge star.

This is the finite-dimensional algebraic core needed before identifying the same
operation with celestial shadow/time reversal.  No claim about the full nonlinear
Penrose-Ward correspondence is made here.
-/

namespace GppGooglyAntiunitaryExchange

open GppHolographicChain

/-- Explicit orientation-reversing anti-linear exchange on the ordered basis
`(e12,e13,e14,e23,e24,e34)` of `∧²ℂ⁴`.  The first three coordinates are conjugated;
the last three are conjugated and sign-reversed. -/
def googlyExchange (v : Fin 6 → ℂ) : Fin 6 → ℂ
  | 0 => star (v 0)
  | 1 => star (v 1)
  | 2 => star (v 2)
  | 3 => -star (v 3)
  | 4 => -star (v 4)
  | 5 => -star (v 5)

/-- The googly exchange is conjugate-linear with respect to the common Plücker
scale.  This is the key compatibility needed for projective descent: multiplying a
bivector by `c` multiplies its googly image by `star c`. -/
theorem googlyExchange_smul (c : ℂ) (v : Fin 6 → ℂ) :
    googlyExchange (c • v) = star c • googlyExchange v := by
  ext i
  fin_cases i <;> simp [googlyExchange, Pi.smul_apply]

/-- The googly exchange is an involution. -/
theorem googlyExchange_involutive (v : Fin 6 → ℂ) :
    googlyExchange (googlyExchange v) = v := by
  ext i
  fin_cases i <;> simp [googlyExchange]

/-- The googly exchange preserves the coordinatewise Hermitian norm density. -/
theorem googlyExchange_normSq (v : Fin 6 → ℂ) (i : Fin 6) :
    Complex.normSq (googlyExchange v i) = Complex.normSq (v i) := by
  fin_cases i <;> simp [googlyExchange]

/-- The key googly relation: orientation-reversing conjugation anti-commutes with
Hodge star.  Consequently it exchanges the `+1` and `-1` Hodge eigenspaces. -/
theorem hodgeStar_googlyExchange_anticommute (v : Fin 6 → ℂ) :
    hodgeStar.mulVec (googlyExchange v) =
      (-1 : ℂ) • googlyExchange (hodgeStar.mulVec v) := by
  ext i
  fin_cases i <;>
    simp (config := { decide := true })
      [hodgeStar, googlyExchange, Matrix.mulVec, dotProduct,
       Fin.sum_univ_six, Pi.smul_apply]

/-- Every self-dual mode is sent to an anti-self-dual mode. -/
theorem googlyExchange_selfDual_to_antiSelfDual
    {v : Fin 6 → ℂ} (hv : hodgeStar.mulVec v = v) :
    hodgeStar.mulVec (googlyExchange v) =
      (-1 : ℂ) • googlyExchange v := by
  rw [hodgeStar_googlyExchange_anticommute, hv]

/-- Every anti-self-dual mode is sent back to a self-dual mode. -/
theorem googlyExchange_antiSelfDual_to_selfDual
    {v : Fin 6 → ℂ} (hv : hodgeStar.mulVec v = (-1 : ℂ) • v) :
    hodgeStar.mulVec (googlyExchange v) = googlyExchange v := by
  rw [hodgeStar_googlyExchange_anticommute, hv]
  ext i
  fin_cases i <;> simp [googlyExchange]

/-- The Plücker quadratic form in the basis
`(p01,p02,p03,p12,p13,p23)`.  Its zero locus is the affine cone over the
Plücker quadric containing the decomposable bivectors of `Gr(2,4)`. -/
def pluckerQuadric (v : Fin 6 → ℂ) : ℂ :=
  v 0 * v 5 - v 1 * v 4 + v 2 * v 3

/-- Orientation-reversing conjugation sends the Plücker quadratic form to the
negative complex conjugate of itself.  In particular its zero locus is preserved. -/
theorem googlyExchange_pluckerQuadric (v : Fin 6 → ℂ) :
    pluckerQuadric (googlyExchange v) = -star (pluckerQuadric v) := by
  simp [pluckerQuadric, googlyExchange]
  ring

/-- Hence the antiunitary googly exchange preserves the Plücker quadric. -/
theorem googlyExchange_preserves_plucker_quadric
    {v : Fin 6 → ℂ} (hv : pluckerQuadric v = 0) :
    pluckerQuadric (googlyExchange v) = 0 := by
  rw [googlyExchange_pluckerQuadric, hv]
  simp

/-- Plücker coordinates of an actual two-frame, packaged in the same six-coordinate
basis used by `hodgeStar` and `googlyExchange`. -/
def pluckerVector (v1 v2 : Fin 4 → ℂ) : Fin 6 → ℂ
  | 0 => plucker v1 v2 0 1
  | 1 => plucker v1 v2 0 2
  | 2 => plucker v1 v2 0 3
  | 3 => plucker v1 v2 1 2
  | 4 => plucker v1 v2 1 3
  | 5 => plucker v1 v2 2 3

/-- Every actual two-frame lands on the Plücker quadric. -/
theorem pluckerVector_quadric_zero (v1 v2 : Fin 4 → ℂ) :
    pluckerQuadric (pluckerVector v1 v2) = 0 := by
  simpa [pluckerQuadric, pluckerVector] using plucker_relation v1 v2

/-- **Googly exchange preserves decomposability at the Plücker-polynomial level.**
For every actual two-frame in `ℂ⁴`, its antiunitary orientation-reversed conjugate
still lies on the Plücker quadric.  This is the exact algebraic bridge needed before
constructing the corresponding map on projective `Gr(2,4)` itself. -/
theorem googlyExchange_pluckerVector_quadric_zero (v1 v2 : Fin 4 → ℂ) :
    pluckerQuadric (googlyExchange (pluckerVector v1 v2)) = 0 := by
  exact googlyExchange_preserves_plucker_quadric (pluckerVector_quadric_zero v1 v2)

end GppGooglyAntiunitaryExchange

#print axioms GppGooglyAntiunitaryExchange.googlyExchange_smul
#print axioms GppGooglyAntiunitaryExchange.googlyExchange_involutive
#print axioms GppGooglyAntiunitaryExchange.googlyExchange_normSq
#print axioms GppGooglyAntiunitaryExchange.hodgeStar_googlyExchange_anticommute
#print axioms GppGooglyAntiunitaryExchange.googlyExchange_selfDual_to_antiSelfDual
#print axioms GppGooglyAntiunitaryExchange.googlyExchange_antiSelfDual_to_selfDual
#print axioms GppGooglyAntiunitaryExchange.googlyExchange_pluckerQuadric
#print axioms GppGooglyAntiunitaryExchange.googlyExchange_preserves_plucker_quadric
#print axioms GppGooglyAntiunitaryExchange.pluckerVector_quadric_zero
#print axioms GppGooglyAntiunitaryExchange.googlyExchange_pluckerVector_quadric_zero