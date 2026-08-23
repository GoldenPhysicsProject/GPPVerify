import GppVerify.RiemannHypothesis.EulerFactorLogDeriv
import Mathlib.Tactic

/-!
# Prime occupation bridge

The local Euler logarithmic derivative has exactly the algebraic form of a geometric
occupation response.

For `n(z) = z/(1-z)`, the identity

  n(z) = z + z n(z)

is the recursive geometric occupation law. Each local prime response is precisely
`log p * n(exp(-s log p))`. Equivalently, away from the Bose denominator pole,

  -zeta_p'(s)/zeta_p(s) = log(p) / (exp(s log p) - 1).

Thus the prime-power tower is exactly the same denominator algebra as a bosonic mode of
energy `log p`. The physical interpretation is separate; the identities here are exact.
-/

namespace GppPrimeOccupation

open Complex

/-- Geometric occupation response. -/
noncomputable def occupation (z : ℂ) : ℂ := z / (1 - z)

/-- Recursive occupation identity `n = z + z n`. -/
theorem occupation_recursion {z : ℂ} (hz : 1 - z ≠ 0) :
    occupation z = z + z * occupation z := by
  unfold occupation
  field_simp [hz]
  ring

/-- The genuine local Euler negative logarithmic derivative is a weighted occupation response. -/
theorem minusLogDerivZetaP_eq_log_mul_occupation (p : ℝ) (s : ℂ) :
    GppCutkoskyWeil.minusLogDerivZetaP p s =
      Complex.log p * occupation (Complex.exp (-s * Complex.log p)) := by
  unfold occupation GppCutkoskyWeil.minusLogDerivZetaP

/-- **Bose-Einstein form of the local prime response.**  Whenever the occupation denominator
is nonzero, the local Euler negative logarithmic derivative is exactly
`log p / (exp(s log p)-1)`. -/
theorem minusLogDerivZetaP_eq_bose (p : ℝ) (s : ℂ)
    (hden : Complex.exp (s * Complex.log p) - 1 ≠ 0) :
    GppCutkoskyWeil.minusLogDerivZetaP p s =
      Complex.log p / (Complex.exp (s * Complex.log p) - 1) := by
  unfold GppCutkoskyWeil.minusLogDerivZetaP
  have hE : Complex.exp (s * Complex.log p) ≠ 0 := Complex.exp_ne_zero _
  have hneg : Complex.exp (-s * Complex.log p) =
      (Complex.exp (s * Complex.log p))⁻¹ := by
    rw [show -s * Complex.log p = -(s * Complex.log p) by ring, Complex.exp_neg]
  rw [hneg]
  field_simp [hE, hden]

end GppPrimeOccupation

#print axioms GppPrimeOccupation.occupation_recursion
#print axioms GppPrimeOccupation.minusLogDerivZetaP_eq_log_mul_occupation
#print axioms GppPrimeOccupation.minusLogDerivZetaP_eq_bose
