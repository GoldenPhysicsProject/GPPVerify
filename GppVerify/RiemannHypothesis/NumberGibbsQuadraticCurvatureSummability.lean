import GppVerify.RiemannHypothesis.NumberGibbsQuadraticConfinement
import Mathlib.Tactic

/-!
# Sixth-order summability for quadratic number-Gibbs curvature

The scalar-curvature Gram reduction uses centered moments through order six.
Quadratic confinement already transfers any zeta-envelope moment once the
corresponding one-parameter logarithmic moment is summable.  This file closes the
only missing analytic orders, five and six, by iterating Mathlib's `logMul`
abscissa invariance, then transfers them to every `β : ℝ`, `η > 0`.
-/

namespace GppNumberGibbsQuadraticCurvatureSummability

open Complex LSeries
open GppZetaGibbsSummability
open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticConfinement

/-- The fifth logarithmic coefficient sequence has abscissa of absolute convergence
at most one. -/
lemma real_log_fifth_abscissa_le_one :
    LSeries.abscissaOfAbsConv
      (fun n : ℕ => (((Real.log n) ^ 5 : ℝ) : ℂ)) ≤ 1 := by
  calc
    LSeries.abscissaOfAbsConv
        (fun n : ℕ => (((Real.log n) ^ 5 : ℝ) : ℂ)) =
      LSeries.abscissaOfAbsConv
        (LSeries.logMul
          (LSeries.logMul
            (LSeries.logMul
              (LSeries.logMul
                (LSeries.logMul (fun _ : ℕ => (1 : ℂ))))))) := by
        apply LSeries.abscissaOfAbsConv_congr
        intro n hn
        simp [LSeries.logMul, Complex.natCast_log, pow_succ, pow_two] <;> ring
    _ = LSeries.abscissaOfAbsConv (fun _ : ℕ => (1 : ℂ)) := by
      simp
    _ ≤ 1 := constant_abscissa_le_one

/-- The sixth logarithmic coefficient sequence has abscissa of absolute convergence
at most one. -/
lemma real_log_sixth_abscissa_le_one :
    LSeries.abscissaOfAbsConv
      (fun n : ℕ => (((Real.log n) ^ 6 : ℝ) : ℂ)) ≤ 1 := by
  calc
    LSeries.abscissaOfAbsConv
        (fun n : ℕ => (((Real.log n) ^ 6 : ℝ) : ℂ)) =
      LSeries.abscissaOfAbsConv
        (LSeries.logMul
          (LSeries.logMul
            (LSeries.logMul
              (LSeries.logMul
                (LSeries.logMul
                  (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))))))) := by
        apply LSeries.abscissaOfAbsConv_congr
        intro n hn
        simp [LSeries.logMul, Complex.natCast_log, pow_succ, pow_two] <;> ring
    _ = LSeries.abscissaOfAbsConv (fun _ : ℕ => (1 : ℂ)) := by
      simp
    _ ≤ 1 := constant_abscissa_le_one

/-- The fifth one-parameter zeta-Gibbs log moment is absolutely summable on `β > 1`. -/
theorem summable_gibbsWeight_mul_logEnergy_fifth {β : ℝ} (hβ : 1 < β) :
    Summable (fun n => gibbsWeight β n * (logEnergy n) ^ 5) := by
  have habs :
      LSeries.abscissaOfAbsConv
          (fun n : ℕ => (((Real.log n) ^ 5 : ℝ) : ℂ)) < β :=
    real_log_fifth_abscissa_le_one.trans_lt (by exact_mod_cast hβ)
  have hbase : Summable (fun n : ℕ => (Real.log n) ^ 5 / (n : ℝ) ^ β) :=
    LSeries.summable_real_of_abscissaOfAbsConv_lt habs
  have hshift := (_root_.summable_nat_add_iff 1).2 hbase
  exact hshift.congr (fun n => by
    simp [gibbsWeight, logEnergy, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
      mul_comm])

/-- The sixth one-parameter zeta-Gibbs log moment is absolutely summable on `β > 1`. -/
theorem summable_gibbsWeight_mul_logEnergy_sixth {β : ℝ} (hβ : 1 < β) :
    Summable (fun n => gibbsWeight β n * (logEnergy n) ^ 6) := by
  have habs :
      LSeries.abscissaOfAbsConv
          (fun n : ℕ => (((Real.log n) ^ 6 : ℝ) : ℂ)) < β :=
    real_log_sixth_abscissa_le_one.trans_lt (by exact_mod_cast hβ)
  have hbase : Summable (fun n : ℕ => (Real.log n) ^ 6 / (n : ℝ) ^ β) :=
    LSeries.summable_real_of_abscissaOfAbsConv_lt habs
  have hshift := (_root_.summable_nat_add_iff 1).2 hbase
  exact hshift.congr (fun n => by
    simp [gibbsWeight, logEnergy, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
      mul_comm])

/-- Every fifth log-energy moment of the quadratically confined number gas is
summable, for arbitrary real `β` and positive confinement `η`. -/
theorem summable_numberGibbs_moment_fifth_of_eta_pos
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable
      (fun n : ℕ =>
        numberGibbsWeight β η n * numberLogEnergy n ^ 5) := by
  apply summable_numberGibbs_moment_of_quadratic β η 5 hη
  exact summable_gibbsWeight_mul_logEnergy_fifth (β := 2) (by norm_num)

/-- Every sixth log-energy moment of the quadratically confined number gas is
summable, for arbitrary real `β` and positive confinement `η`. -/
theorem summable_numberGibbs_moment_sixth_of_eta_pos
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable
      (fun n : ℕ =>
        numberGibbsWeight β η n * numberLogEnergy n ^ 6) := by
  apply summable_numberGibbs_moment_of_quadratic β η 6 hη
  exact summable_gibbsWeight_mul_logEnergy_sixth (β := 2) (by norm_num)

end GppNumberGibbsQuadraticCurvatureSummability

#print axioms GppNumberGibbsQuadraticCurvatureSummability.real_log_fifth_abscissa_le_one
#print axioms GppNumberGibbsQuadraticCurvatureSummability.real_log_sixth_abscissa_le_one
#print axioms GppNumberGibbsQuadraticCurvatureSummability.summable_gibbsWeight_mul_logEnergy_fifth
#print axioms GppNumberGibbsQuadraticCurvatureSummability.summable_gibbsWeight_mul_logEnergy_sixth
#print axioms GppNumberGibbsQuadraticCurvatureSummability.summable_numberGibbs_moment_fifth_of_eta_pos
#print axioms GppNumberGibbsQuadraticCurvatureSummability.summable_numberGibbs_moment_sixth_of_eta_pos
