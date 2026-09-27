import GppVerify.RiemannHypothesis.PrimeFisherCountableGeometry
import GppVerify.RiemannHypothesis.PrimeHankelAllOrderStrict
import GppVerify.RiemannHypothesis.WeightedVarianceInfiniteStrict
import Mathlib.Tactic

/-!
# Probability normalization of the countable prime-Fisher measure

The arithmetic Fisher weight

  w_beta(n) = Lambda(n) log(n) exp(-beta log n)

has already been proved summable and to have strictly positive total mass for
`beta > 1`.  This file performs the probability normalization explicitly.  The
result is the honest countable probability measure needed before defining
expectations, covariance, entropy, and fluctuation geometry directly for the
prime-power Fisher ensemble.

No finite truncation is used in the normalization.
-/

namespace GppPrimeFisherProbability

open GppCountableFisherMomentLimit
open GppPrimeFisherMomentSummability
open GppPrimeHankelFisherSpecialization
open GppPrimeFisherCountableGeometry
open GppPrimeHankelAllOrderStrict
open GppWeightedVarianceInfiniteStrict

/-- Total mass of the arithmetic Fisher measure. -/
noncomputable def primeFisherMass (beta : ℝ) : ℝ :=
  infiniteMoment (fisherWeight beta) Real.log 0

/-- Probability-normalized arithmetic Fisher weight. -/
noncomputable def primeFisherProbability (beta : ℝ) (n : ℕ) : ℝ :=
  fisherWeight beta n / primeFisherMass beta

/-- Expectation with respect to the normalized countable prime-Fisher ensemble. -/
noncomputable def primeFisherExpectation (beta : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, primeFisherProbability beta n * f n

/-- Normalized variance of the logarithmic energy observable. -/
noncomputable def primeFisherLogVariance (beta : ℝ) : ℝ :=
  primeFisherExpectation beta (fun n : ℕ => (Real.log n) ^ 2) -
    (primeFisherExpectation beta (fun n : ℕ => Real.log n)) ^ 2

/-- The total Fisher mass is strictly positive on the thermodynamic half-line. -/
theorem primeFisherMass_pos {beta : ℝ} (hbeta : 1 < beta) :
    0 < primeFisherMass beta := by
  simpa [primeFisherMass] using prime_fisher_mass_pos hbeta

/-- Each normalized prime-Fisher weight is nonnegative. -/
theorem primeFisherProbability_nonneg {beta : ℝ} (hbeta : 1 < beta) (n : ℕ) :
    0 ≤ primeFisherProbability beta n := by
  exact div_nonneg (fisherWeight_nonneg beta n) (primeFisherMass_pos hbeta).le

/-- The unnormalized Fisher weights sum exactly to their mass definition. -/
theorem fisherWeight_tsum_eq_mass (beta : ℝ) :
    (∑' n : ℕ, fisherWeight beta n) = primeFisherMass beta := by
  simp [primeFisherMass, infiniteMoment]

/-- **Prime-Fisher probability normalization.** For every `beta > 1`, the
actual countable von-Mangoldt Fisher weights normalize to total mass one. -/
theorem primeFisherProbability_tsum_eq_one {beta : ℝ} (hbeta : 1 < beta) :
    (∑' n : ℕ, primeFisherProbability beta n) = 1 := by
  have hmass : primeFisherMass beta ≠ 0 := (primeFisherMass_pos hbeta).ne'
  rw [show (∑' n : ℕ, primeFisherProbability beta n) =
      (∑' n : ℕ, fisherWeight beta n) / primeFisherMass beta by
        simp only [primeFisherProbability, tsum_div_const]]
  rw [fisherWeight_tsum_eq_mass]
  exact div_self hmass

/-- The normalized arithmetic Fisher weights are summable on `beta > 1`. -/
theorem summable_primeFisherProbability {beta : ℝ} (hbeta : 1 < beta) :
    Summable (primeFisherProbability beta) := by
  have hs : Summable (fun n : ℕ => fisherWeight beta n) := by
    simpa using summable_fisherWeight_mul_log_pow 0 hbeta
  simpa only [primeFisherProbability] using hs.div_const (primeFisherMass beta)

/-- **Normalized raw-moment bridge.** Every logarithmic expectation under the
prime-Fisher probability distribution is exactly the corresponding unnormalized
countable Fisher moment divided by the total mass. This is the direct bridge from
the existing Hankel/Fisher moment hierarchy to probability expectations. -/
theorem primeFisherExpectation_log_pow_eq_moment_div_mass
    (r : ℕ) (beta : ℝ) :
    primeFisherExpectation beta (fun n : ℕ => (Real.log n) ^ r) =
      infiniteMoment (fisherWeight beta) Real.log r / primeFisherMass beta := by
  unfold primeFisherExpectation primeFisherProbability infiniteMoment
  rw [← tsum_div_const]
  apply tsum_congr
  intro n
  ring

/-- The normalized logarithmic variance written directly in terms of the
unnormalized Fisher moments is strictly positive for every `beta > 1`.
The strictness is supplied by the two distinct positive prime-power support
points `2` and `4`, through the general countable weighted-variance theorem. -/
theorem primeFisher_normalized_log_variance_pos
    {beta : ℝ} (hbeta : 1 < beta) :
    0 < infiniteMoment (fisherWeight beta) Real.log 2 / primeFisherMass beta -
      (infiniteMoment (fisherWeight beta) Real.log 1 / primeFisherMass beta) ^ 2 := by
  have hW : Summable (fun n : ℕ => fisherWeight beta n) := by
    simpa using summable_fisherWeight_mul_log_pow 0 hbeta
  have hM : Summable (fun n : ℕ => fisherWeight beta n * Real.log n) := by
    simpa using summable_fisherWeight_mul_log_pow 1 hbeta
  have hQ : Summable (fun n : ℕ => fisherWeight beta n * (Real.log n) ^ 2) := by
    simpa using summable_fisherWeight_mul_log_pow 2 hbeta
  have hWpos : 0 < ∑' n : ℕ, fisherWeight beta n := by
    rw [fisherWeight_tsum_eq_mass]
    exact primeFisherMass_pos hbeta
  have hw2 : 0 < fisherWeight beta 2 := by
    simpa using (fisherWeight_two_pow_pos (β := beta) 0)
  have hw4 : 0 < fisherWeight beta 4 := by
    simpa using (fisherWeight_two_pow_pos (β := beta) 1)
  have hlog : Real.log (2 : ℝ) ≠ Real.log (4 : ℝ) := by
    exact ne_of_lt (Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num))
  have hvar := normalized_weighted_variance_pos_tsum
    (fun n : ℕ => fisherWeight beta n) (fun n : ℕ => Real.log n)
    (fisherWeight_nonneg beta) hW hM hQ hWpos hw2 hw4 (by simpa using hlog)
  simpa [primeFisherMass, infiniteMoment] using hvar

/-- **Strict normalized prime-Fisher fluctuation.**  The actual probability
ensemble has positive variance in the logarithmic energy observable everywhere
on the thermodynamic half-line `beta > 1`; it is never a delta distribution. -/
theorem primeFisherLogVariance_pos {beta : ℝ} (hbeta : 1 < beta) :
    0 < primeFisherLogVariance beta := by
  have h2 := primeFisherExpectation_log_pow_eq_moment_div_mass 2 beta
  have h1 := primeFisherExpectation_log_pow_eq_moment_div_mass 1 beta
  simp only [pow_one] at h1
  unfold primeFisherLogVariance
  rw [h2, h1]
  exact primeFisher_normalized_log_variance_pos hbeta

end GppPrimeFisherProbability

#print axioms GppPrimeFisherProbability.primeFisherMass_pos
#print axioms GppPrimeFisherProbability.primeFisherProbability_nonneg
#print axioms GppPrimeFisherProbability.primeFisherProbability_tsum_eq_one
#print axioms GppPrimeFisherProbability.summable_primeFisherProbability
#print axioms GppPrimeFisherProbability.primeFisherExpectation_log_pow_eq_moment_div_mass
#print axioms GppPrimeFisherProbability.primeFisher_normalized_log_variance_pos
#print axioms GppPrimeFisherProbability.primeFisherLogVariance_pos
