import GppVerify.RiemannHypothesis.NumberGibbsTwoParameterStrict
import GppVerify.RiemannHypothesis.ZetaGibbsSummability
import Mathlib.Tactic

/-!
# Zeta-half-plane summability wedge for the confined number-Gibbs family

For `η ≥ 0`, the quadratic factor can only decrease
`exp (-β log(n+1))`. Hence the ordinary zeta-Gibbs moment estimates for
`β > 1` dominate all moments through order four, making the strict Fisher
specialization unconditional on this half-plane.
-/

namespace GppNumberGibbsTwoParameterZetaWedge

open GppNumberGibbsTwoParameterStrict
open GppZetaGibbsSummability
open GppCountableFisherMomentLimit
open GppFiniteFisherMomentBridge

lemma numberLogEnergy_nonneg (n : ℕ) : 0 ≤ numberLogEnergy n := by
  unfold numberLogEnergy
  apply Real.log_nonneg
  norm_num

lemma numberGibbsWeight_le_exp_zeta
    (β η : ℝ) (hη : 0 ≤ η) (n : ℕ) :
    numberGibbsWeight β η n ≤ Real.exp (-β * numberLogEnergy n) := by
  unfold numberGibbsWeight numberLogEnergy
  apply Real.exp_le_exp.mpr
  have hs : 0 ≤ η * (Real.log (n + 1 : ℝ)) ^ 2 :=
    mul_nonneg hη (sq_nonneg _)
  linarith

lemma exp_zeta_eq_gibbsWeight (β : ℝ) (n : ℕ) :
    Real.exp (-β * numberLogEnergy n) = gibbsWeight β n := by
  unfold numberLogEnergy gibbsWeight
  have hx : 0 < (n + 1 : ℝ) := by positivity
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Real.rpow_def_of_pos hx, one_div, ← Real.exp_neg]
  congr 1
  ring

lemma summable_numberGibbs_moment_of_zeta
    (β η : ℝ) (r : ℕ) (hη : 0 ≤ η)
    (hz : Summable (fun n : ℕ => gibbsWeight β n * logEnergy n ^ r)) :
    Summable (fun n : ℕ =>
      numberGibbsWeight β η n * numberLogEnergy n ^ r) := by
  refine Summable.of_nonneg_of_le ?_ ?_ hz
  · intro n
    exact mul_nonneg (numberGibbsWeight_nonneg β η n)
      (pow_nonneg (numberLogEnergy_nonneg n) r)
  · intro n
    have hw : numberGibbsWeight β η n ≤ gibbsWeight β n := by
      calc
        numberGibbsWeight β η n ≤ Real.exp (-β * numberLogEnergy n) :=
          numberGibbsWeight_le_exp_zeta β η hη n
        _ = gibbsWeight β n := exp_zeta_eq_gibbsWeight β n
    have hp : 0 ≤ numberLogEnergy n ^ r :=
      pow_nonneg (numberLogEnergy_nonneg n) r
    simpa [numberLogEnergy, logEnergy] using mul_le_mul_of_nonneg_right hw hp

/-- For `β > 1` and `η ≥ 0`, the infinite mass-aware two-parameter number-Gibbs
Fisher numerator is strictly positive with no remaining summability hypotheses. -/
theorem numberGibbs_fisherNumerator_infinite_pos_of_one_lt_beta
    {β η : ℝ} (hβ : 1 < β) (hη : 0 ≤ η) :
    0 < fisherNumerator
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 0)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 1)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 2)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 3)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 4) := by
  have hz0 : Summable (fun n : ℕ => gibbsWeight β n * logEnergy n ^ 0) := by
    simpa using summable_gibbsWeight hβ
  have hz1 : Summable (fun n : ℕ => gibbsWeight β n * logEnergy n ^ 1) := by
    simpa using summable_gibbsWeight_mul_logEnergy hβ
  have hz2 : Summable (fun n : ℕ => gibbsWeight β n * logEnergy n ^ 2) :=
    summable_gibbsWeight_mul_logEnergy_sq hβ
  have hz3 : Summable (fun n : ℕ => gibbsWeight β n * logEnergy n ^ 3) :=
    summable_gibbsWeight_mul_logEnergy_cube hβ
  have hz4 : Summable (fun n : ℕ => gibbsWeight β n * logEnergy n ^ 4) :=
    summable_gibbsWeight_mul_logEnergy_fourth hβ
  apply numberGibbs_fisherNumerator_infinite_pos β η
  · exact summable_numberGibbs_moment_of_zeta β η 0 hη hz0
  · exact summable_numberGibbs_moment_of_zeta β η 1 hη hz1
  · exact summable_numberGibbs_moment_of_zeta β η 2 hη hz2
  · exact summable_numberGibbs_moment_of_zeta β η 3 hη hz3
  · exact summable_numberGibbs_moment_of_zeta β η 4 hη hz4

end GppNumberGibbsTwoParameterZetaWedge

#print axioms GppNumberGibbsTwoParameterZetaWedge.numberGibbs_fisherNumerator_infinite_pos_of_one_lt_beta
