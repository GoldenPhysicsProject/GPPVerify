import GppVerify.RiemannHypothesis.WeightedVarianceInfinite
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Summability of the zeta Gibbs log moments

For real `β > 1` the three real series needed for the Gibbs variance,

  (n+1)^(-β),
  (n+1)^(-β) log(n+1),
  (n+1)^(-β) log(n+1)^2,

are summable. The logarithmically weighted cases are obtained from Mathlib's
L-series abscissa machinery: multiplying coefficients by `log n` does not change
the abscissa of absolute convergence.
-/

namespace GppZetaGibbsSummability

open Complex LSeries

/-- Unnormalized real Gibbs weight on the positive integer `n+1`. -/
noncomputable def gibbsWeight (β : ℝ) (n : ℕ) : ℝ :=
  1 / ((n + 1 : ℕ) : ℝ) ^ β

/-- Arithmetic log-energy observable. -/
noncomputable def logEnergy (n : ℕ) : ℝ :=
  Real.log ((n + 1 : ℕ) : ℝ)

/-- The constant coefficient L-series has abscissa of absolute convergence at most `1`. -/
lemma constant_abscissa_le_one :
    LSeries.abscissaOfAbsConv (fun _ : ℕ => (1 : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_le_const
  exact ⟨1, by intro n hn; simp⟩

/-- The real logarithm coefficient sequence also has abscissa at most `1`. -/
lemma real_log_abscissa_le_one :
    LSeries.abscissaOfAbsConv (fun n : ℕ => (Real.log n : ℂ)) ≤ 1 := by
  calc
    LSeries.abscissaOfAbsConv (fun n : ℕ => (Real.log n : ℂ)) =
        LSeries.abscissaOfAbsConv (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) := by
      apply LSeries.abscissaOfAbsConv_congr
      intro n hn
      simp [LSeries.logMul, Complex.natCast_log]
    _ = LSeries.abscissaOfAbsConv (fun _ : ℕ => (1 : ℂ)) := by
      simp
    _ ≤ 1 := constant_abscissa_le_one

/-- The squared real logarithm coefficient sequence has the same convergence boundary. -/
lemma real_log_sq_abscissa_le_one :
    LSeries.abscissaOfAbsConv (fun n : ℕ => (((Real.log n) ^ 2 : ℝ) : ℂ)) ≤ 1 := by
  calc
    LSeries.abscissaOfAbsConv (fun n : ℕ => (((Real.log n) ^ 2 : ℝ) : ℂ)) =
        LSeries.abscissaOfAbsConv
          (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))) := by
      apply LSeries.abscissaOfAbsConv_congr
      intro n hn
      simp [LSeries.logMul, Complex.natCast_log, pow_two]
    _ = LSeries.abscissaOfAbsConv (fun _ : ℕ => (1 : ℂ)) := by
      simp
    _ ≤ 1 := constant_abscissa_le_one

/-- The Gibbs partition-weight series is summable for `β > 1`. -/
theorem summable_gibbsWeight {β : ℝ} (hβ : 1 < β) :
    Summable (gibbsWeight β) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ β) :=
    Real.summable_one_div_nat_rpow.mpr hβ
  have hshift := (_root_.summable_nat_add_iff 1).2 hbase
  exact hshift.congr (fun n => by
    simp [gibbsWeight, one_div, Nat.cast_add, Nat.cast_one])

/-- The first log-energy moment is absolutely summable for `β > 1`. -/
theorem summable_gibbsWeight_mul_logEnergy {β : ℝ} (hβ : 1 < β) :
    Summable (fun n => gibbsWeight β n * logEnergy n) := by
  have habs : LSeries.abscissaOfAbsConv (fun n : ℕ => (Real.log n : ℂ)) < β :=
    real_log_abscissa_le_one.trans_lt (by exact_mod_cast hβ)
  have hbase : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ β) :=
    LSeries.summable_real_of_abscissaOfAbsConv_lt habs
  have hshift := (_root_.summable_nat_add_iff 1).2 hbase
  exact hshift.congr (fun n => by
    simp [gibbsWeight, logEnergy, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
      mul_comm])

/-- The second log-energy moment is absolutely summable for `β > 1`. -/
theorem summable_gibbsWeight_mul_logEnergy_sq {β : ℝ} (hβ : 1 < β) :
    Summable (fun n => gibbsWeight β n * (logEnergy n) ^ 2) := by
  have habs : LSeries.abscissaOfAbsConv (fun n : ℕ => (((Real.log n) ^ 2 : ℝ) : ℂ)) < β :=
    real_log_sq_abscissa_le_one.trans_lt (by exact_mod_cast hβ)
  have hbase : Summable (fun n : ℕ => (Real.log n) ^ 2 / (n : ℝ) ^ β) :=
    LSeries.summable_real_of_abscissaOfAbsConv_lt habs
  have hshift := (_root_.summable_nat_add_iff 1).2 hbase
  exact hshift.congr (fun n => by
    simp [gibbsWeight, logEnergy, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
      mul_comm])

/-- The total unnormalized Gibbs weight is strictly positive. -/
theorem gibbsWeight_tsum_pos {β : ℝ} (hβ : 1 < β) :
    0 < ∑' n, gibbsWeight β n := by
  have hnonneg : ∀ n, 0 ≤ gibbsWeight β n := by
    intro n
    unfold gibbsWeight
    positivity
  have hzero : 0 < gibbsWeight β 0 := by
    unfold gibbsWeight
    norm_num
  exact (summable_gibbsWeight hβ).tsum_pos hnonneg 0 hzero

/-- The zeta Gibbs variance is nonnegative directly from countable weighted variance. -/
theorem gibbs_logEnergy_variance_nonneg {β : ℝ} (hβ : 1 < β) :
    0 ≤ (∑' n, gibbsWeight β n * (logEnergy n) ^ 2) / (∑' n, gibbsWeight β n) -
      ((∑' n, gibbsWeight β n * logEnergy n) / (∑' n, gibbsWeight β n)) ^ 2 := by
  apply GppWeightedVarianceInfinite.normalized_weighted_variance_nonneg_tsum
  · intro n
    unfold gibbsWeight
    positivity
  · exact summable_gibbsWeight hβ
  · exact summable_gibbsWeight_mul_logEnergy hβ
  · exact summable_gibbsWeight_mul_logEnergy_sq hβ
  · exact gibbsWeight_tsum_pos hβ

end GppZetaGibbsSummability

#print axioms GppZetaGibbsSummability.summable_gibbsWeight
#print axioms GppZetaGibbsSummability.summable_gibbsWeight_mul_logEnergy
#print axioms GppZetaGibbsSummability.summable_gibbsWeight_mul_logEnergy_sq
#print axioms GppZetaGibbsSummability.gibbsWeight_tsum_pos
#print axioms GppZetaGibbsSummability.gibbs_logEnergy_variance_nonneg
