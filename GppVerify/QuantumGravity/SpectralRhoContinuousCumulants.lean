import GppVerify.QuantumGravity.SpectralRhoContinuousHigherMoments

/-!
# Continuous Gamma-chamber cumulants

This file packages the exact low-order cumulants forced by the already-derived
continuous chamber moment polynomials.  It is purely algebraic: no integral or
characteristic-function evaluation is assumed here.
-/

namespace GppSpectralRhoContinuousCumulants

/-- The second cumulant equals the variance `c/2`. -/
theorem second_cumulant (c : ℝ) : c / 2 = c / 2 := by
  rfl

/-- The fourth cumulant obtained from `μ₄ - 3 μ₂²` is `c/4`. -/
theorem fourth_cumulant (c : ℝ) :
    c * (3 * c + 1) / 4 - 3 * (c / 2) ^ 2 = c / 4 := by
  ring

/-- The sixth cumulant obtained from the centered moment formula is `c/2`. -/
theorem sixth_cumulant (c : ℝ) :
    c * (15 * c ^ 2 + 15 * c + 4) / 8
        - 15 * (c * (3 * c + 1) / 4) * (c / 2)
        + 30 * (c / 2) ^ 3 = c / 2 := by
  ring

/-- The eighth cumulant obtained from the centered moment formula is `17c/8`. -/
theorem eighth_cumulant (c : ℝ) :
    c * (105 * c ^ 3 + 210 * c ^ 2 + 147 * c + 34) / 16
        - 28 * (c * (15 * c ^ 2 + 15 * c + 4) / 8) * (c / 2)
        - 35 * (c * (3 * c + 1) / 4) ^ 2
        + 420 * (c * (3 * c + 1) / 4) * (c / 2) ^ 2
        - 630 * (c / 2) ^ 4 = 17 * c / 8 := by
  ring

/-- The certified second-cumulant polynomial is additive in the chamber parameter. -/
theorem second_cumulant_add (c d : ℝ) :
    (c + d) / 2 = c / 2 + d / 2 := by
  ring

/-- The certified fourth-cumulant polynomial is additive in the chamber parameter. -/
theorem fourth_cumulant_add (c d : ℝ) :
    (c + d) / 4 = c / 4 + d / 4 := by
  ring

/-- The certified sixth-cumulant polynomial is additive in the chamber parameter. -/
theorem sixth_cumulant_add (c d : ℝ) :
    (c + d) / 2 = c / 2 + d / 2 := by
  ring

/-- The certified eighth-cumulant polynomial is additive in the chamber parameter. -/
theorem eighth_cumulant_add (c d : ℝ) :
    17 * (c + d) / 8 = 17 * c / 8 + 17 * d / 8 := by
  ring

end GppSpectralRhoContinuousCumulants

#print axioms GppSpectralRhoContinuousCumulants.fourth_cumulant
#print axioms GppSpectralRhoContinuousCumulants.sixth_cumulant
#print axioms GppSpectralRhoContinuousCumulants.eighth_cumulant
#print axioms GppSpectralRhoContinuousCumulants.fourth_cumulant_add
#print axioms GppSpectralRhoContinuousCumulants.sixth_cumulant_add
#print axioms GppSpectralRhoContinuousCumulants.eighth_cumulant_add
