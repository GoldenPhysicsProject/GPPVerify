import Mathlib.Tactic

/-!
# Prime modular covariance identities

Elementary algebraic identities underlying the finite-place modular dictionary.

The prime Boltzmann weight is q_p = 1/p. Its bosonic covariance is

  C_p = q_p / (1-q_p) = 1/(p-1),

so the finite-place mass-square coordinate is 4 C_p.

The odd/even repetition decomposition

  x/(1-x) = x/(1-x^2) + x^2/(1-x^2)

identifies the two repetition channels with the anomalous and normal
two-mode covariance functions at real half-density.

These are local algebraic identities only. They do not prove RH or a global
adelic positivity theorem.
-/

namespace GppPrimeModularCovariance

def thermalCov (q : ℝ) : ℝ := q / (1 - q)

def normalCov (r : ℝ) : ℝ := r ^ 2 / (1 - r ^ 2)

def anomalousCov (r : ℝ) : ℝ := r / (1 - r ^ 2)

theorem thermalCov_prime (p : ℝ) (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    thermalCov (1 / p) = 1 / (p - 1) := by
  unfold thermalCov
  field_simp
  ring

theorem casimirMassSq_prime (p : ℝ) (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    4 * thermalCov (1 / p) = 4 / (p - 1) := by
  rw [thermalCov_prime p hp0 hp1]

theorem prime_from_covariance (p : ℝ) (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    1 + 1 / thermalCov (1 / p) = p := by
  rw [thermalCov_prime p hp0 hp1]
  field_simp
  ring

theorem thermalCov_sq (r : ℝ) :
    thermalCov (r ^ 2) = normalCov r := by
  rfl

theorem anomalous_sq_eq_normal_mul (r : ℝ) (h : 1 - r ^ 2 ≠ 0) :
    anomalousCov r ^ 2 = normalCov r * (1 + normalCov r) := by
  unfold anomalousCov normalCov
  field_simp [h]
  ring

theorem odd_even_repetition_split (x : ℝ)
    (h1 : 1 - x ≠ 0) (h2 : 1 - x ^ 2 ≠ 0) :
    x / (1 - x) = x / (1 - x ^ 2) + x ^ 2 / (1 - x ^ 2) := by
  field_simp [h1, h2]
  ring

theorem odd_channel_eq_anomalous (r : ℝ) :
    r / (1 - r ^ 2) = anomalousCov r := by
  rfl

theorem even_channel_eq_normal (r : ℝ) :
    r ^ 2 / (1 - r ^ 2) = normalCov r := by
  rfl

end GppPrimeModularCovariance

#print axioms GppPrimeModularCovariance.thermalCov_prime
#print axioms GppPrimeModularCovariance.casimirMassSq_prime
#print axioms GppPrimeModularCovariance.prime_from_covariance
#print axioms GppPrimeModularCovariance.anomalous_sq_eq_normal_mul
#print axioms GppPrimeModularCovariance.odd_even_repetition_split
