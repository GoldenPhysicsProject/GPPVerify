import GppVerify.RiemannHypothesis.ZetaGibbsFisher
import GppVerify.RiemannHypothesis.WeightedVarianceInfiniteStrict
import Mathlib.Tactic

/-!
# Strict thermodynamic stability of the zeta Gibbs gas

The honest Gibbs distribution already has two positive support points with distinct
log-energies: `n = 0` has energy `log 1 = 0`, while `n = 1` has energy `log 2 > 0`.
The generic strict weighted-variance theorem therefore upgrades the existing weak
thermodynamic inequalities without using the stale von-Mangoldt strict-derivative chain.
-/

namespace GppZetaGibbsStrictThermodynamics

open GppZetaGibbsSummability
open GppZetaGibbsFisher
open GppWeightedVarianceInfiniteStrict

/-- The genuine zeta-Gibbs log-energy variance is strictly positive for `β > 1`. -/
theorem logEnergyVariance_pos {β : ℝ} (hβ : 1 < β) :
    0 < logEnergyVariance β := by
  have hw : ∀ n, 0 ≤ gibbsWeight β n := by
    intro n
    unfold gibbsWeight
    positivity
  have hw0 : 0 < gibbsWeight β 0 := by
    unfold gibbsWeight
    norm_num
  have hw1 : 0 < gibbsWeight β 1 := by
    unfold gibbsWeight
    positivity
  have hx01 : logEnergy 0 ≠ logEnergy 1 := by
    simp only [logEnergy, Nat.cast_add, Nat.cast_zero, Nat.cast_one]
    norm_num
    exact ne_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  unfold logEnergyVariance M2 M1 Z
  exact normalized_weighted_variance_pos_tsum
    (gibbsWeight β) logEnergy hw
    (summable_gibbsWeight hβ)
    (summable_gibbsWeight_mul_logEnergy hβ)
    (summable_gibbsWeight_mul_logEnergy_sq hβ)
    (gibbsWeight_tsum_pos hβ)
    hw0 hw1 hx01

/-- Strict positivity of the real zeta susceptibility / Fisher response on the
honest Gibbs axis. -/
theorem zetaVarianceResponse_re_pos {β : ℝ} (hβ : 1 < β) :
    0 < (zetaVarianceResponse β).re := by
  rw [zetaVarianceResponse_eq_ofReal_logEnergyVariance hβ]
  simpa using logEnergyVariance_pos hβ

/-- Strict positive heat capacity on the honest Gibbs domain. -/
theorem heatCapacity_pos {β : ℝ} (hβ : 1 < β) :
    0 < heatCapacity β := by
  unfold heatCapacity
  have hβ0 : 0 < β := lt_trans (by norm_num) hβ
  exact mul_pos (sq_pos_of_pos hβ0) (logEnergyVariance_pos hβ)

/-- The entropy response is strictly negative with inverse temperature. -/
theorem entropyBetaDerivative_neg {β : ℝ} (hβ : 1 < β) :
    entropyBetaDerivative β < 0 := by
  unfold entropyBetaDerivative
  have hβ0 : 0 < β := lt_trans (by norm_num) hβ
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hβ0) (logEnergyVariance_pos hβ)

/-- Consequently the entropy response cannot vanish anywhere on the honest Gibbs domain. -/
theorem entropyBetaDerivative_ne_zero {β : ℝ} (hβ : 1 < β) :
    entropyBetaDerivative β ≠ 0 := by
  exact ne_of_lt (entropyBetaDerivative_neg hβ)

/-- Exact thermodynamic response identity: heat capacity is `-β` times the entropy
response. This is algebraic and therefore does not require differentiability hypotheses. -/
theorem heatCapacity_eq_neg_beta_mul_entropyBetaDerivative (β : ℝ) :
    heatCapacity β = -β * entropyBetaDerivative β := by
  unfold heatCapacity entropyBetaDerivative
  ring

/-- On any nonzero inverse temperature, the entropy response is exactly heat capacity
divided by `-β`. -/
theorem entropyBetaDerivative_eq_neg_heatCapacity_div_beta
    {β : ℝ} (hβ : β ≠ 0) :
    entropyBetaDerivative β = -heatCapacity β / β := by
  unfold heatCapacity entropyBetaDerivative
  field_simp [hβ]
  ring

/-- On the honest Gibbs domain the ratio of positive heat capacity to the positive
entropy-loss rate recovers the inverse temperature exactly. -/
theorem heatCapacity_div_neg_entropyBetaDerivative_eq_beta
    {β : ℝ} (hβ : 1 < β) :
    heatCapacity β / (-entropyBetaDerivative β) = β := by
  have hne : entropyBetaDerivative β ≠ 0 := entropyBetaDerivative_ne_zero hβ
  rw [heatCapacity_eq_neg_beta_mul_entropyBetaDerivative]
  field_simp [hne]

/-- The Fisher metric coefficient is exactly heat capacity divided by `β²`. -/
theorem heatCapacity_div_beta_sq_eq_variance
    {β : ℝ} (hβ : β ≠ 0) :
    heatCapacity β / β ^ 2 = logEnergyVariance β := by
  unfold heatCapacity
  field_simp [hβ]

/-- The same Fisher metric coefficient is the entropy-loss rate divided by `β`. -/
theorem neg_entropyBetaDerivative_div_beta_eq_variance
    {β : ℝ} (hβ : β ≠ 0) :
    (-entropyBetaDerivative β) / β = logEnergyVariance β := by
  unfold entropyBetaDerivative
  field_simp [hβ]

/-- On `β>1`, the three positive fluctuation observables satisfy an exact quadratic
response identity: entropy-loss-rate squared divided by heat capacity equals the
Fisher variance. -/
theorem neg_entropyBetaDerivative_sq_div_heatCapacity_eq_variance
    {β : ℝ} (hβ : 1 < β) :
    (-entropyBetaDerivative β) ^ 2 / heatCapacity β = logEnergyVariance β := by
  have hC : heatCapacity β ≠ 0 := ne_of_gt (heatCapacity_pos hβ)
  rw [neg_sq, entropyBetaDerivative_sq_eq_heatCapacity_mul_variance]
  field_simp [hC]

/-- Strict positivity of the Fisher variance makes the inverse temperature itself
recoverable from entropy loss per unit Fisher fluctuation. -/
theorem neg_entropyBetaDerivative_div_variance_eq_beta
    {β : ℝ} (hβ : 1 < β) :
    (-entropyBetaDerivative β) / logEnergyVariance β = β := by
  have hV : logEnergyVariance β ≠ 0 := ne_of_gt (logEnergyVariance_pos hβ)
  unfold entropyBetaDerivative
  field_simp [hV]

/-- Heat capacity per unit Fisher variance is exactly the squared inverse temperature. -/
theorem heatCapacity_div_variance_eq_beta_sq
    {β : ℝ} (hβ : 1 < β) :
    heatCapacity β / logEnergyVariance β = β ^ 2 := by
  have hV : logEnergyVariance β ≠ 0 := ne_of_gt (logEnergyVariance_pos hβ)
  unfold heatCapacity
  field_simp [hV]

end GppZetaGibbsStrictThermodynamics

#print axioms GppZetaGibbsStrictThermodynamics.logEnergyVariance_pos
#print axioms GppZetaGibbsStrictThermodynamics.zetaVarianceResponse_re_pos
#print axioms GppZetaGibbsStrictThermodynamics.heatCapacity_pos
#print axioms GppZetaGibbsStrictThermodynamics.entropyBetaDerivative_neg
#print axioms GppZetaGibbsStrictThermodynamics.entropyBetaDerivative_ne_zero
#print axioms GppZetaGibbsStrictThermodynamics.heatCapacity_eq_neg_beta_mul_entropyBetaDerivative
#print axioms GppZetaGibbsStrictThermodynamics.entropyBetaDerivative_eq_neg_heatCapacity_div_beta
#print axioms GppZetaGibbsStrictThermodynamics.heatCapacity_div_neg_entropyBetaDerivative_eq_beta
#print axioms GppZetaGibbsStrictThermodynamics.heatCapacity_div_beta_sq_eq_variance
#print axioms GppZetaGibbsStrictThermodynamics.neg_entropyBetaDerivative_div_beta_eq_variance
#print axioms GppZetaGibbsStrictThermodynamics.neg_entropyBetaDerivative_sq_div_heatCapacity_eq_variance
#print axioms GppZetaGibbsStrictThermodynamics.neg_entropyBetaDerivative_div_variance_eq_beta
#print axioms GppZetaGibbsStrictThermodynamics.heatCapacity_div_variance_eq_beta_sq
