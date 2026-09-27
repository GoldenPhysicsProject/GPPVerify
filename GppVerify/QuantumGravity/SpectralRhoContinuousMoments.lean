import GppVerify.QuantumGravity.SpectralRhoContinuousStep

/-!
# Continuous Gamma-chamber moment consequences

This file extracts exact algebraic consequences of the continuous chamber step
recurrence.  No integral evaluation is assumed here beyond whatever moment values
are explicitly supplied to the hypotheses.

For the normalized continuous Gamma chamber, the recurrence

  M_{2m}(c+1) = 2 (c^2 M_{2m}(c) + M_{2m+2}(c)) / (c(2c+1))

together with the already-forced second moment `M₂(c)=c/2` recursively determines
higher even moments.  The first two consequences are

  M₄(c) = c(3c+1)/4,
  M₆(c) = c(15c²+15c+4)/8.

The first formula also gives excess kurtosis `1/c` when `c>0`.
-/

namespace GppSpectralRhoContinuousMoments

/-- The chamber step for the second moment, together with `M₂(c)=c/2` and
`M₂(c+1)=(c+1)/2`, forces the fourth moment `M₄(c)=c(3c+1)/4`. -/
theorem second_moment_step_forces_fourth_moment
    (c m4 : ℝ) (hc : 0 < c)
    (hstep :
      (c + 1) / 2 =
        2 * (c ^ 2 * (c / 2) + m4) / (c * (2 * c + 1))) :
    m4 = c * (3 * c + 1) / 4 := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hlin : 2 * c + 1 ≠ 0 := by nlinarith
  field_simp [hc0, hlin] at hstep
  nlinarith

/-- Feeding the exact fourth moments at chambers `c` and `c+1` into the same
recurrence forces the sixth moment `M₆(c)=c(15c²+15c+4)/8`. -/
theorem fourth_moment_step_forces_sixth_moment
    (c m6 : ℝ) (hc : 0 < c)
    (hstep :
      (c + 1) * (3 * (c + 1) + 1) / 4 =
        2 * (c ^ 2 * (c * (3 * c + 1) / 4) + m6) /
          (c * (2 * c + 1))) :
    m6 = c * (15 * c ^ 2 + 15 * c + 4) / 8 := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hlin : 2 * c + 1 ≠ 0 := by nlinarith
  field_simp [hc0, hlin] at hstep
  nlinarith

/-- For the normalized chamber moment formulas `M₂=c/2` and
`M₄=c(3c+1)/4`, the excess kurtosis is exactly `1/c`. -/
theorem excess_kurtosis_eq_inv
    (c : ℝ) (hc : 0 < c) :
    (c * (3 * c + 1) / 4) / (c / 2) ^ 2 - 3 = 1 / c := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  field_simp [hc0]
  ring

end GppSpectralRhoContinuousMoments

#print axioms GppSpectralRhoContinuousMoments.second_moment_step_forces_fourth_moment
#print axioms GppSpectralRhoContinuousMoments.fourth_moment_step_forces_sixth_moment
#print axioms GppSpectralRhoContinuousMoments.excess_kurtosis_eq_inv
