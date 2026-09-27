import GppVerify.RiemannHypothesis.CountableFisherStrictWitness
import Mathlib.Tactic

/-!
# Strict two-parameter number-Gibbs Fisher geometry

This module specializes the generic countable three-state Fisher witness to the
quadratically confined number-Gibbs family

  w_{β,η}(n) = exp(-β log(n+1) - η (log(n+1))^2),
  x(n) = log(n+1).

The finite-to-countable algebraic strictness is unconditional once raw moments
through order four are summable.  Analytic summability is intentionally kept as
an explicit hypothesis here, so this theorem does not hide the remaining
countable convergence input.
-/

namespace GppNumberGibbsTwoParameterStrict

open GppCountableFisherMomentLimit
open GppCountableFisherStrictWitness
open GppFiniteFisherMomentBridge

/-- Unnormalized two-parameter number-Gibbs weight on the positive integers,
indexed by `n : ℕ` through `n+1`. -/
noncomputable def numberGibbsWeight (β η : ℝ) (n : ℕ) : ℝ :=
  Real.exp
    (-β * Real.log (n + 1 : ℝ) - η * (Real.log (n + 1 : ℝ)) ^ 2)

/-- Logarithmic number observable. -/
noncomputable def numberLogEnergy (n : ℕ) : ℝ :=
  Real.log (n + 1 : ℝ)

/-- Every number-Gibbs weight is strictly positive. -/
theorem numberGibbsWeight_pos (β η : ℝ) (n : ℕ) :
    0 < numberGibbsWeight β η n := by
  unfold numberGibbsWeight
  exact Real.exp_pos _

/-- Every number-Gibbs weight is nonnegative. -/
theorem numberGibbsWeight_nonneg (β η : ℝ) (n : ℕ) :
    0 ≤ numberGibbsWeight β η n :=
  (numberGibbsWeight_pos β η n).le

/-- The first three logarithmic number energies are exactly `0`, `log 2`, `log 3`. -/
theorem first_three_numberLogEnergy :
    numberLogEnergy 0 = 0 ∧
      numberLogEnergy 1 = Real.log 2 ∧
      numberLogEnergy 2 = Real.log 3 := by
  constructor
  · simp [numberLogEnergy]
  constructor <;> norm_num [numberLogEnergy]

/-- The first three logarithmic number energies are pairwise distinct. -/
theorem first_three_numberLogEnergy_pairwise_distinct :
    numberLogEnergy 0 ≠ numberLogEnergy 1 ∧
      numberLogEnergy 0 ≠ numberLogEnergy 2 ∧
      numberLogEnergy 1 ≠ numberLogEnergy 2 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have h23 : Real.log (2 : ℝ) < Real.log 3 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [first_three_numberLogEnergy.1,
    first_three_numberLogEnergy.2.1,
    first_three_numberLogEnergy.2.2]
  exact ⟨ne_of_lt hlog2, ne_of_lt hlog3, ne_of_lt h23⟩

/-- **Strict countable number-Gibbs Fisher numerator.** For the quadratically
confined number-Gibbs family, raw-moment summability through order four plus the
fixed arithmetic states `1,2,3` forces strict positivity of the infinite
mass-aware Fisher numerator. -/
theorem numberGibbs_fisherNumerator_infinite_pos
    (β η : ℝ)
    (h0 : Summable (fun n : ℕ =>
      numberGibbsWeight β η n * numberLogEnergy n ^ 0))
    (h1 : Summable (fun n : ℕ =>
      numberGibbsWeight β η n * numberLogEnergy n ^ 1))
    (h2 : Summable (fun n : ℕ =>
      numberGibbsWeight β η n * numberLogEnergy n ^ 2))
    (h3 : Summable (fun n : ℕ =>
      numberGibbsWeight β η n * numberLogEnergy n ^ 3))
    (h4 : Summable (fun n : ℕ =>
      numberGibbsWeight β η n * numberLogEnergy n ^ 4)) :
    0 < fisherNumerator
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 0)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 1)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 2)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 3)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 4) := by
  rcases first_three_numberLogEnergy_pairwise_distinct with ⟨h01, h02, h12⟩
  exact fisherNumerator_infinite_pos_of_fixed_positive_distinct_witness
    (numberGibbsWeight β η) numberLogEnergy
    (numberGibbsWeight_nonneg β η)
    0 1 2
    (numberGibbsWeight_pos β η 0)
    (numberGibbsWeight_pos β η 1)
    (numberGibbsWeight_pos β η 2)
    h01 h02 h12 h0 h1 h2 h3 h4

end GppNumberGibbsTwoParameterStrict

#print axioms GppNumberGibbsTwoParameterStrict.numberGibbsWeight_pos
#print axioms GppNumberGibbsTwoParameterStrict.first_three_numberLogEnergy_pairwise_distinct
#print axioms GppNumberGibbsTwoParameterStrict.numberGibbs_fisherNumerator_infinite_pos
