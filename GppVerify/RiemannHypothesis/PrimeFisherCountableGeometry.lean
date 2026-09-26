import GppVerify.RiemannHypothesis.CountableFisherMomentLimit
import GppVerify.RiemannHypothesis.PrimeFisherMomentSummability
import GppVerify.RiemannHypothesis.PrimeHankelAllOrderStrict
import Mathlib.Tactic

/-!
# Countable prime-gas Fisher geometry

This file specializes the general countable Fisher/Vandermonde positivity theorem to the
actual arithmetic Fisher weight

  w_beta(n) = Lambda(n) log(n) exp(-beta log n),

with observable `x(n) = log n`.  The all-order logarithmic summability theorem supplies
raw moments through order four for every `beta > 1`; pointwise nonnegativity of the
von-Mangoldt Fisher weight then gives a nonnegative mass-aware covariance numerator.

No normalization of finite truncations is used.  The total countable mass is proved
strictly positive, so the raw moments can then be divided by that mass.  The normalized
covariance determinant is the mass-aware numerator divided by the fourth power of the
mass and is therefore nonnegative.
-/

namespace GppPrimeFisherCountableGeometry

open GppCountableFisherMomentLimit
open GppPrimeFisherMomentSummability
open GppPrimeHankelFisherSpecialization
open GppPrimeHankelAllOrderStrict
open GppFiniteFisherMomentBridge

/-- Every raw logarithmic moment of the arithmetic Fisher weight is summable on `beta > 1`,
expressed in the generic `infiniteMoment` interface used by the countable Fisher theorem. -/
theorem summable_prime_fisher_moment (r : ℕ) {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ => fisherWeight β n * (Real.log n) ^ r) := by
  exact summable_fisherWeight_mul_log_pow r hβ

/-- **The full arithmetic Fisher measure has strictly positive finite mass.**
This is obtained from the already-proved all-order strict polynomial Gram theorem by
specializing the polynomial to the constant `1`.  It is the denominator certificate
needed before normalizing the countable Fisher measure to a probability distribution. -/
theorem prime_fisher_mass_pos {β : ℝ} (hβ : 1 < β) :
    0 < infiniteMoment (fisherWeight β) Real.log 0 := by
  have h := fisher_polynomial_tsum_pos_unconditional hβ (1 : Polynomial ℝ) (by norm_num)
  simpa [infiniteMoment] using h

/-- **Countable arithmetic Fisher positivity.**  On the half-plane `beta > 1`, the
mass-aware covariance numerator for the sufficient statistics `log n` and `(log n)^2`
is nonnegative for the full countable von-Mangoldt Fisher measure. -/
theorem prime_fisherNumerator_infinite_nonneg {β : ℝ} (hβ : 1 < β) :
    0 ≤ fisherNumerator
      (infiniteMoment (fisherWeight β) Real.log 0)
      (infiniteMoment (fisherWeight β) Real.log 1)
      (infiniteMoment (fisherWeight β) Real.log 2)
      (infiniteMoment (fisherWeight β) Real.log 3)
      (infiniteMoment (fisherWeight β) Real.log 4) := by
  apply fisherNumerator_infinite_nonneg
  · intro n
    exact fisherWeight_nonneg β n
  · simpa using summable_fisherWeight_mul_log_pow 0 hβ
  · simpa using summable_fisherWeight_mul_log_pow 1 hβ
  · simpa using summable_fisherWeight_mul_log_pow 2 hβ
  · simpa using summable_fisherWeight_mul_log_pow 3 hβ
  · simpa using summable_fisherWeight_mul_log_pow 4 hβ

/-- **Normalized countable prime-Fisher determinant is nonnegative.**
Writing `m_r` for the full raw moments and `m_0 > 0` for the total Fisher mass,
the covariance determinant of the probability-normalized moments `m_r / m_0` is
exactly `fisherNumerator m_0 ... m_4 / m_0^4`.  Thus normalization introduces no
finite-truncation assumption and preserves positivity. -/
theorem prime_fisher_normalized_det_nonneg {β : ℝ} (hβ : 1 < β) :
    let m0 := infiniteMoment (fisherWeight β) Real.log 0
    let m1 := infiniteMoment (fisherWeight β) Real.log 1
    let m2 := infiniteMoment (fisherWeight β) Real.log 2
    let m3 := infiniteMoment (fisherWeight β) Real.log 3
    let m4 := infiniteMoment (fisherWeight β) Real.log 4
    0 ≤ fisherDet (m1 / m0) (m2 / m0) (m3 / m0) (m4 / m0) := by
  dsimp
  let m0 := infiniteMoment (fisherWeight β) Real.log 0
  let m1 := infiniteMoment (fisherWeight β) Real.log 1
  let m2 := infiniteMoment (fisherWeight β) Real.log 2
  let m3 := infiniteMoment (fisherWeight β) Real.log 3
  let m4 := infiniteMoment (fisherWeight β) Real.log 4
  have hm0 : 0 < m0 := by
    simpa [m0] using prime_fisher_mass_pos hβ
  have hnum : 0 ≤ fisherNumerator m0 m1 m2 m3 m4 := by
    simpa [m0, m1, m2, m3, m4] using prime_fisherNumerator_infinite_nonneg hβ
  have hid :
      fisherDet (m1 / m0) (m2 / m0) (m3 / m0) (m4 / m0) =
        fisherNumerator m0 m1 m2 m3 m4 / m0 ^ 4 := by
    unfold fisherDet fisherNumerator
    field_simp [ne_of_gt hm0]
    ring
  rw [hid]
  exact div_nonneg hnum (pow_nonneg m0 4)

end GppPrimeFisherCountableGeometry

#print axioms GppPrimeFisherCountableGeometry.prime_fisher_mass_pos
#print axioms GppPrimeFisherCountableGeometry.prime_fisherNumerator_infinite_nonneg
#print axioms GppPrimeFisherCountableGeometry.prime_fisher_normalized_det_nonneg