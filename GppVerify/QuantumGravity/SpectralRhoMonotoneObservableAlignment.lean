import GppVerify.QuantumGravity.SpectralRhoContinuousStep

/-!
# Monotone radial observable alignment for continuous Gamma chambers

This module supplies the pointwise Chebyshev/rearrangement sign input needed for the
measure-theoretic covariance step in continuous Gamma-chamber ordering.  It does not
assume the analytic Gamma-density realization.
-/

namespace GppSpectralRhoContinuousStep

/-- Exact factorization for an arbitrary radial observable `g`.  The chamber-step
increment is a positive scalar multiple of the radial-square increment. -/
theorem continuousStepFactor_observable_alignment_identity
    (c x y : ℝ) (g : ℝ → ℝ) (hc : 0 < c) :
    (g (y ^ 2) - g (x ^ 2)) *
        (continuousStepFactor c y - continuousStepFactor c x) =
      2 / (c * (2 * c + 1)) *
        ((g (y ^ 2) - g (x ^ 2)) * (y ^ 2 - x ^ 2)) := by
  rw [continuousStepFactor_radial_difference c x y hc]
  ring

/-- If `g` is pairwise monotone on the two radial values under consideration, its
increment is aligned nonnegatively with the chamber likelihood-ratio increment. -/
theorem continuousStepFactor_observable_alignment_nonneg
    (c x y : ℝ) (g : ℝ → ℝ) (hc : 0 < c)
    (hg : 0 ≤ (g (y ^ 2) - g (x ^ 2)) * (y ^ 2 - x ^ 2)) :
    0 ≤ (g (y ^ 2) - g (x ^ 2)) *
      (continuousStepFactor c y - continuousStepFactor c x) := by
  rw [continuousStepFactor_observable_alignment_identity c x y g hc]
  have hcoef : 0 ≤ 2 / (c * (2 * c + 1)) := by positivity
  exact mul_nonneg hcoef hg

/-- Strict pairwise radial monotonicity gives strict alignment with the chamber
likelihood-ratio increment. -/
theorem continuousStepFactor_observable_alignment_pos
    (c x y : ℝ) (g : ℝ → ℝ) (hc : 0 < c)
    (hg : 0 < (g (y ^ 2) - g (x ^ 2)) * (y ^ 2 - x ^ 2)) :
    0 < (g (y ^ 2) - g (x ^ 2)) *
      (continuousStepFactor c y - continuousStepFactor c x) := by
  rw [continuousStepFactor_observable_alignment_identity c x y g hc]
  have hcoef : 0 < 2 / (c * (2 * c + 1)) := by positivity
  exact mul_pos hcoef hg

end GppSpectralRhoContinuousStep
