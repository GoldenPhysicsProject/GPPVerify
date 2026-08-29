import GppVerify.RiemannHypothesis.ZetaGibbsMoments
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Bridge from L-series logarithmic insertions to real Gibbs moments

For real `β > 1`, the constant-one L-series and its first four logarithmic coefficient
insertions are exactly the complex embeddings of the unnormalized real Gibbs partition
sum and the first four log-energy moments. This closes the indexing and coercion
interface between the L-series derivative formalism and real Gibbs cumulants.
-/

namespace GppZetaGibbsMomentBridge

open Complex LSeries
open GppZetaGibbsSummability

open scoped Topology

/-- Complex powers of a positive real `n + 1` agree with embedded real powers. -/
lemma natSucc_cpow_eq_ofReal_rpow (n : ℕ) (β : ℝ) :
    (((n : ℂ) + 1) ^ (β : ℂ)) = ((((n : ℝ) + 1) ^ β : ℝ) : ℂ) := by
  simpa using
    (Complex.ofReal_cpow (show 0 ≤ (n : ℝ) + 1 by positivity) β).symm

/-- Complex logarithms of positive real `n + 1` agree with embedded real logarithms. -/
lemma natSucc_clog_eq_ofReal_log (n : ℕ) :
    Complex.log ((n : ℂ) + 1) =
      (Real.log ((n : ℝ) + 1) : ℂ) := by
  simpa using
    (Complex.ofReal_log (show 0 ≤ (n : ℝ) + 1 by positivity)).symm

/-- The constant-one L-series on the real axis is the embedded real Gibbs partition sum. -/
theorem LSeries_one_eq_ofReal_gibbsWeight_tsum {β : ℝ} (hβ : 1 < β) :
    LSeries (fun _ : ℕ => (1 : ℂ)) (β : ℂ) =
      ((∑' n, gibbsWeight β n : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold LSeries
  have hs : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) (β : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (constant_abscissa_le_one.trans_lt (by exact_mod_cast hβ))
  change Summable (fun n => LSeries.term (fun _ : ℕ => (1 : ℂ)) (β : ℂ) n) at hs
  rw [hs.tsum_eq_zero_add]
  have hzero : LSeries.term (fun _ : ℕ => (1 : ℂ)) (β : ℂ) 0 = 0 := by
    simp [LSeries.term]
  rw [hzero, zero_add]
  apply tsum_congr
  intro n
  simp [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), gibbsWeight]
  exact natSucc_cpow_eq_ofReal_rpow n β

/-- One logarithmic L-series insertion is the embedded first Gibbs log-energy moment. -/
theorem LSeries_logMul_one_eq_ofReal_firstMoment {β : ℝ} (hβ : 1 < β) :
    LSeries (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) (β : ℂ) =
      ((∑' n, gibbsWeight β n * logEnergy n : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold LSeries
  have hs : LSeriesSummable (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) (β : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simpa using constant_abscissa_le_one.trans_lt (by exact_mod_cast hβ))
  change Summable
    (fun n => LSeries.term (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) (β : ℂ) n) at hs
  rw [hs.tsum_eq_zero_add]
  have hzero : LSeries.term (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) (β : ℂ) 0 = 0 := by
    simp [LSeries.term]
  rw [hzero, zero_add]
  apply tsum_congr
  intro n
  simp [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), LSeries.logMul,
    gibbsWeight, logEnergy, Complex.natCast_log, div_eq_mul_inv]
  rw [natSucc_cpow_eq_ofReal_rpow n β, natSucc_clog_eq_ofReal_log n]
  norm_cast
  ring

/-- Two logarithmic L-series insertions give the embedded second Gibbs log-energy moment. -/
theorem LSeries_logMul_logMul_one_eq_ofReal_secondMoment {β : ℝ} (hβ : 1 < β) :
    LSeries (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))) (β : ℂ) =
      ((∑' n, gibbsWeight β n * (logEnergy n) ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold LSeries
  have hs : LSeriesSummable
      (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))) (β : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simpa using constant_abscissa_le_one.trans_lt (by exact_mod_cast hβ))
  change Summable
    (fun n => LSeries.term
      (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))) (β : ℂ) n) at hs
  rw [hs.tsum_eq_zero_add]
  have hzero : LSeries.term
      (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))) (β : ℂ) 0 = 0 := by
    simp [LSeries.term]
  rw [hzero, zero_add]
  apply tsum_congr
  intro n
  simp [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), LSeries.logMul,
    gibbsWeight, logEnergy, Complex.natCast_log, pow_two, div_eq_mul_inv]
  rw [natSucc_cpow_eq_ofReal_rpow n β, natSucc_clog_eq_ofReal_log n]
  norm_cast
  ring

/-- Three logarithmic L-series insertions give the embedded third Gibbs log-energy moment. -/
theorem LSeries_logMul_logMul_logMul_one_eq_ofReal_thirdMoment {β : ℝ} (hβ : 1 < β) :
    LSeries
      (LSeries.logMul
        (LSeries.logMul
          (LSeries.logMul (fun _ : ℕ => (1 : ℂ))))) (β : ℂ) =
      ((∑' n, gibbsWeight β n * (logEnergy n) ^ 3 : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold LSeries
  have hs : LSeriesSummable
      (LSeries.logMul
        (LSeries.logMul
          (LSeries.logMul (fun _ : ℕ => (1 : ℂ))))) (β : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simpa using constant_abscissa_le_one.trans_lt (by exact_mod_cast hβ))
  change Summable
    (fun n => LSeries.term
      (LSeries.logMul
        (LSeries.logMul
          (LSeries.logMul (fun _ : ℕ => (1 : ℂ))))) (β : ℂ) n) at hs
  rw [hs.tsum_eq_zero_add]
  have hzero : LSeries.term
      (LSeries.logMul
        (LSeries.logMul
          (LSeries.logMul (fun _ : ℕ => (1 : ℂ))))) (β : ℂ) 0 = 0 := by
    simp [LSeries.term]
  rw [hzero, zero_add]
  apply tsum_congr
  intro n
  simp [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), LSeries.logMul,
    gibbsWeight, logEnergy, Complex.natCast_log, pow_succ, div_eq_mul_inv]
  rw [natSucc_cpow_eq_ofReal_rpow n β, natSucc_clog_eq_ofReal_log n]
  norm_cast
  ring

/-- Four logarithmic L-series insertions give the embedded fourth Gibbs log-energy moment. -/
theorem LSeries_logMul_four_one_eq_ofReal_fourthMoment {β : ℝ} (hβ : 1 < β) :
    LSeries
      (LSeries.logMul
        (LSeries.logMul
          (LSeries.logMul
            (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))))) (β : ℂ) =
      ((∑' n, gibbsWeight β n * (logEnergy n) ^ 4 : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold LSeries
  have hs : LSeriesSummable
      (LSeries.logMul
        (LSeries.logMul
          (LSeries.logMul
            (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))))) (β : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simpa using constant_abscissa_le_one.trans_lt (by exact_mod_cast hβ))
  change Summable
    (fun n => LSeries.term
      (LSeries.logMul
        (LSeries.logMul
          (LSeries.logMul
            (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))))) (β : ℂ) n) at hs
  rw [hs.tsum_eq_zero_add]
  have hzero : LSeries.term
      (LSeries.logMul
        (LSeries.logMul
          (LSeries.logMul
            (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))))) (β : ℂ) 0 = 0 := by
    simp [LSeries.term]
  rw [hzero, zero_add]
  apply tsum_congr
  intro n
  simp [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), LSeries.logMul,
    gibbsWeight, logEnergy, Complex.natCast_log, pow_succ, div_eq_mul_inv]
  rw [natSucc_cpow_eq_ofReal_rpow n β, natSucc_clog_eq_ofReal_log n]
  norm_cast
  ring

end GppZetaGibbsMomentBridge

#print axioms GppZetaGibbsMomentBridge.natSucc_cpow_eq_ofReal_rpow
#print axioms GppZetaGibbsMomentBridge.natSucc_clog_eq_ofReal_log
#print axioms GppZetaGibbsMomentBridge.LSeries_one_eq_ofReal_gibbsWeight_tsum
#print axioms GppZetaGibbsMomentBridge.LSeries_logMul_one_eq_ofReal_firstMoment
#print axioms GppZetaGibbsMomentBridge.LSeries_logMul_logMul_one_eq_ofReal_secondMoment
#print axioms GppZetaGibbsMomentBridge.LSeries_logMul_logMul_logMul_one_eq_ofReal_thirdMoment
#print axioms GppZetaGibbsMomentBridge.LSeries_logMul_four_one_eq_ofReal_fourthMoment
