import GppVerify.QuantumGravity.SpectralRhoContinuousMoments

/-!
# Higher continuous Gamma-chamber moment consequences

This file continues the exact algebraic moment recursion for the normalized
continuous Gamma chamber.  It does not evaluate any integral.  The sole input
is the chamber-step recurrence together with the previously forced sixth
moment polynomial.
-/

namespace GppSpectralRhoContinuousHigherMoments

/-- Feeding the exact sixth moments at chambers `c` and `c+1` into the chamber
step forces the eighth moment

  M₈(c) = c(105c³ + 210c² + 147c + 34)/16.
-/
theorem sixth_moment_step_forces_eighth_moment
    (c m8 : ℝ) (hc : 0 < c)
    (hstep :
      (c + 1) * (15 * (c + 1) ^ 2 + 15 * (c + 1) + 4) / 8 =
        2 *
            (c ^ 2 * (c * (15 * c ^ 2 + 15 * c + 4) / 8) + m8) /
          (c * (2 * c + 1))) :
    m8 = c * (105 * c ^ 3 + 210 * c ^ 2 + 147 * c + 34) / 16 := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hlin : 2 * c + 1 ≠ 0 := by nlinarith
  field_simp [hc0, hlin] at hstep
  nlinarith

/-- At the celestial spectral chamber `c=1`, the forced eighth moment is
`M₈(1)=31`. -/
theorem chamber_one_eighth_moment :
    (1 : ℝ) * (105 * (1 : ℝ) ^ 3 + 210 * (1 : ℝ) ^ 2 + 147 * (1 : ℝ) + 34) / 16 = 31 := by
  norm_num

end GppSpectralRhoContinuousHigherMoments

#print axioms GppSpectralRhoContinuousHigherMoments.sixth_moment_step_forces_eighth_moment
#print axioms GppSpectralRhoContinuousHigherMoments.chamber_one_eighth_moment
