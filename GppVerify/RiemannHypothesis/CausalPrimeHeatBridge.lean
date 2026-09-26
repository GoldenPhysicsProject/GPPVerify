import GppVerify.RiemannHypothesis.CausalPrimeResolventFinite
import GppVerify.RiemannHypothesis.VonMangoldtPrimePowerTower
import Mathlib.Tactic

/-!
# Causal prime anomaly to normalized von-Mangoldt heat term

The causal Dirichlet-heat boundary anomaly at the prime repetition
`a = (m+1) log p`, weighted by the Euler-log resolvent coefficient, has already been
reduced to

  (log p / sqrt(p^(m+1))) g_t((m+1) log p),

where `g_t` is the normalized heat Gaussian.  For an actual prime, the standard identities

  Lambda(p^(m+1)) = log p,
  log(p^(m+1)) = (m+1) log p

show that this is literally the normalized von-Mangoldt heat summand at the natural number
`p^(m+1)`.

This closes the local arithmetic identification.  Infinite repetition and prime sums, and
the relative Archimedean trace, remain separate analytic steps.
-/

namespace GppCausalPrimeHeatBridge

open GppCausalHeatBoundaryAnomaly
open GppCausalPrimeResolventFinite

/-- Normalized von-Mangoldt heat summand.  `HeatTraceCriterion.primeSide_heatGaussian`
uses the same term with the common normalization `1/sqrt(4*pi*t)` factored outside. -/
noncomputable def normalizedPrimeHeatSummand (t : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
    heatKernelGaussian t (Real.log n)

/-- Prime-power logarithmic coordinate agrees exactly with the causal repetition length. -/
theorem log_primePow_eq_repetitionLength
    (p : Nat.Primes) (m : ℕ) :
    Real.log ((p : ℕ) ^ repetition m) =
      repetitionLength (p : ℝ) m := by
  simpa [repetitionLength] using
    (Real.log_pow (p : ℝ) (repetition m))

/-- **Exact local causal/prime-heat bridge.** Each weighted causal repetition anomaly is
literally the normalized von-Mangoldt heat summand of the corresponding prime power. -/
theorem weighted_causal_anomaly_eq_normalizedPrimeHeatSummand
    (p : Nat.Primes) (t : ℝ) (m : ℕ) :
    resolventWeight (p : ℝ) m *
        scalarHeatAnomaly t (repetitionLength (p : ℝ) m) =
      normalizedPrimeHeatSummand t ((p : ℕ) ^ repetition m) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.prop.pos
  have hv :
      ArithmeticFunction.vonMangoldt ((p : ℕ) ^ repetition m) =
        Real.log (p : ℕ) := by
    simpa [repetition] using
      (GppVonMangoldtPrimePowerTower.vonMangoldt_prime_pow (p : ℕ) m p.prop)
  rw [resolventWeight_mul_scalarHeatAnomaly_eq_sqrt_weight hpR]
  unfold normalizedPrimeHeatSummand
  rw [hv, Nat.cast_pow, log_primePow_eq_repetitionLength p m]

/-- Finite repetition sums therefore coincide term-by-term with the corresponding finite
prime-power heat tower. -/
theorem finiteResolventAnomaly_eq_normalizedPrimePowerHeatTower
    (p : Nat.Primes) (t : ℝ) (M : ℕ) :
    finiteResolventAnomaly (p : ℝ) t M =
      ∑ m in Finset.range M,
        normalizedPrimeHeatSummand t ((p : ℕ) ^ repetition m) := by
  unfold finiteResolventAnomaly
  apply Finset.sum_congr rfl
  intro m hm
  exact weighted_causal_anomaly_eq_normalizedPrimeHeatSummand p t m

end GppCausalPrimeHeatBridge

#print axioms GppCausalPrimeHeatBridge.log_primePow_eq_repetitionLength
#print axioms GppCausalPrimeHeatBridge.weighted_causal_anomaly_eq_normalizedPrimeHeatSummand
#print axioms GppCausalPrimeHeatBridge.finiteResolventAnomaly_eq_normalizedPrimePowerHeatTower
