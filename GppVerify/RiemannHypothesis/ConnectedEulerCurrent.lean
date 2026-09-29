import GppVerify.RiemannHypothesis.ZetaGibbsSummability
import Mathlib.Tactic

/-!
# Connected Euler-current summability thresholds

This module certifies the elementary analytic core behind the connected
half-density logarithmic Euler current.

The scalar Dirichlet logarithmic current uses an L1-type weight with exponent
1/2 + a and is summable by the existing zeta-Gibbs machinery once a > 1/2.
The Hilbert-square majorant uses exponent 1 + 2a and is summable for every
a > 0.

This is a domain theorem only. It does not prove RH and does not assert that
the scalar completed logarithmic derivative extends past its Euler domain.
-/

namespace GppConnectedEulerCurrent

open GppZetaGibbsSummability

/--
The square-majorant for a half-density logarithmic current is summable for
every positive displacement a.

Analytically this is
sum (log(n+1))^2 / (n+1)^(1+2a) < infinity,
the L2 threshold corresponding to Re(s - 1/2) = a > 0.
-/
theorem summable_log_sq_halfDensity
    {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ =>
      (Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 /
        (((n + 1 : ℕ) : ℝ) ^ (1 + 2 * a))) := by
  have hβ : (1 : ℝ) < 1 + 2 * a := by linarith
  have h :=
    GppZetaGibbsSummability.summable_gibbsWeight_mul_logEnergy_sq hβ
  exact h.congr (fun n => by
    simp [GppZetaGibbsSummability.gibbsWeight,
      GppZetaGibbsSummability.logEnergy, div_eq_mul_inv, mul_comm])

/--
The corresponding scalar logarithmic majorant is summable in the ordinary
Euler domain a > 1/2.

Analytically this is
sum log(n+1) / (n+1)^(1/2+a) < infinity.
-/
theorem summable_log_halfDensity_scalar
    {a : ℝ} (ha : (1 : ℝ) / 2 < a) :
    Summable (fun n : ℕ =>
      Real.log ((n + 1 : ℕ) : ℝ) /
        (((n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + a))) := by
  have hβ : (1 : ℝ) < (1 : ℝ) / 2 + a := by linarith
  have h :=
    GppZetaGibbsSummability.summable_gibbsWeight_mul_logEnergy hβ
  exact h.congr (fun n => by
    simp [GppZetaGibbsSummability.gibbsWeight,
      GppZetaGibbsSummability.logEnergy, div_eq_mul_inv, mul_comm])

end GppConnectedEulerCurrent

#print axioms GppConnectedEulerCurrent.summable_log_sq_halfDensity
#print axioms GppConnectedEulerCurrent.summable_log_halfDensity_scalar
