import GppVerify.CelestialHolography.GooglyAntiunitaryExchange
import Mathlib.Tactic

/-!
# Twistor-space lift of the googly exchange

The six-coordinate antiunitary googly exchange on `Λ² ℂ⁴` is not merely an
ad hoc bivector operation.  It is the exterior-square action of an explicit
antiunitary involution on the underlying four-component twistor space.

Choose phases

  r₀ = i,   r₁ = r₂ = r₃ = -i.

Then `r₀ rⱼ = +1` for `j=1,2,3`, while `rᵢ rⱼ = -1` for
`1 ≤ i < j ≤ 3`.  Consequently the induced action on the ordered Plücker basis
`(p01,p02,p03,p12,p13,p23)` is exactly

  (+conj,+conj,+conj,-conj,-conj,-conj),

which is `googlyExchange`.
-/

namespace GppGooglyTwistorLift

open GppHolographicChain GppGooglyAntiunitaryExchange

/-- Explicit antiunitary phase-conjugation on four-component twistor coordinates. -/
def twistorGoogly (z : Fin 4 → ℂ) : Fin 4 → ℂ
  | 0 => Complex.I * star (z 0)
  | 1 => -Complex.I * star (z 1)
  | 2 => -Complex.I * star (z 2)
  | 3 => -Complex.I * star (z 3)

/-- The twistor lift is conjugate-linear. -/
theorem twistorGoogly_smul (c : ℂ) (z : Fin 4 → ℂ) :
    twistorGoogly (c • z) = star c • twistorGoogly z := by
  ext i
  fin_cases i <;> simp [twistorGoogly, Pi.smul_apply] <;> ring

/-- The twistor lift squares to the identity. -/
theorem twistorGoogly_involutive (z : Fin 4 → ℂ) :
    twistorGoogly (twistorGoogly z) = z := by
  ext i
  fin_cases i <;> apply Complex.ext <;>
    simp [twistorGoogly, Complex.mul_re, Complex.mul_im] <;> ring

/-- Coordinatewise Hermitian norm density is preserved by the twistor lift. -/
theorem twistorGoogly_normSq (z : Fin 4 → ℂ) (i : Fin 4) :
    Complex.normSq (twistorGoogly z i) = Complex.normSq (z i) := by
  fin_cases i <;> simp [twistorGoogly, Complex.normSq] <;> ring

/-- **Exact exterior-square lift theorem.**  Applying `twistorGoogly` to both vectors
of a two-frame induces exactly the previously formalized six-coordinate
`googlyExchange` on its Plücker bivector. -/
theorem pluckerVector_twistorGoogly (v1 v2 : Fin 4 → ℂ) :
    pluckerVector (twistorGoogly v1) (twistorGoogly v2) =
      googlyExchange (pluckerVector v1 v2) := by
  ext k
  fin_cases k <;> apply Complex.ext <;>
    simp [pluckerVector, plucker, twistorGoogly, googlyExchange,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- Hence every actual two-frame realizes the antiunitary googly exchange already
at twistor level, before projectivization. -/
theorem googlyExchange_pluckerVector_eq_twistorLift
    (v1 v2 : Fin 4 → ℂ) :
    googlyExchange (pluckerVector v1 v2) =
      pluckerVector (twistorGoogly v1) (twistorGoogly v2) := by
  exact (pluckerVector_twistorGoogly v1 v2).symm

end GppGooglyTwistorLift

#print axioms GppGooglyTwistorLift.twistorGoogly_smul
#print axioms GppGooglyTwistorLift.twistorGoogly_involutive
#print axioms GppGooglyTwistorLift.twistorGoogly_normSq
#print axioms GppGooglyTwistorLift.pluckerVector_twistorGoogly
