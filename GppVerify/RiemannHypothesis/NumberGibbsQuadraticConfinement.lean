import GppVerify.RiemannHypothesis.NumberGibbsTwoParameterZetaWedge
import Mathlib.Tactic

/-!
# Quadratic log-confinement for the two-parameter number-Gibbs family

For every real `β` and every `η > 0`, the factor

  exp (-β L - η L^2),  L = log (n+1),

is eventually dominated by the ordinary zeta weight with fixed exponent `2`.
The logarithmic moment factor is left untouched, so the existing zeta-Gibbs
summability theorems at exponent `2` immediately give all moments through
order four.  Combined with the fixed three-state Vandermonde witness, this
removes the last summability assumptions from strict two-parameter Fisher
positivity throughout the quadratically confined region `η > 0`.
-/

namespace GppNumberGibbsQuadraticConfinement

open Filter
open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsTwoParameterZetaWedge
open GppZetaGibbsSummability
open GppCountableFisherMomentLimit
open GppFiniteFisherMomentBridge

/-- The arithmetic log-energy `log (n+1)` tends to `+∞`. -/
lemma numberLogEnergy_tendsto_atTop : Tendsto numberLogEnergy atTop atTop := by
  unfold numberLogEnergy
  exact (Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))

/-- Positive quadratic confinement eventually dominates any fixed linear
shift in the exponent.  We choose the fixed comparison exponent `2`. -/
lemma eventually_numberGibbsWeight_le_gibbsWeight_two
    (β η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, numberGibbsWeight β η n ≤ gibbsWeight 2 n := by
  filter_upwards
      [numberLogEnergy_tendsto_atTop.eventually_ge_atTop ((2 - β) / η)] with n hn
  have hL : 0 ≤ numberLogEnergy n := numberLogEnergy_nonneg n
  have hlinear : 2 - β ≤ η * numberLogEnergy n := by
    have h := (div_le_iff₀ hη).mp hn
    simpa [mul_comm] using h
  have hquad : (2 - β) * numberLogEnergy n ≤
      η * (numberLogEnergy n) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hlinear hL
    nlinarith
  calc
    numberGibbsWeight β η n
        ≤ Real.exp (-2 * numberLogEnergy n) := by
          apply Real.exp_le_exp.mpr
          change -β * numberLogEnergy n - η * numberLogEnergy n ^ 2 ≤
            -2 * numberLogEnergy n
          nlinarith [hquad]
    _ = gibbsWeight 2 n := exp_zeta_eq_gibbsWeight 2 n

/-- Uniform version of quadratic tail domination.  On every parameter region
`β ≥ -B`, `η ≥ η₀ > 0`, one common arithmetic tail is dominated by the same
fixed zeta weight of exponent `2`.  This is the local-uniform estimate needed
for differentiation under the countable partition sum: compact parameter
neighborhoods may be enclosed in such a region, and logarithmic derivative
factors can then be handled by the existing zeta-moment summability lemmas. -/
lemma eventually_numberGibbsWeight_le_gibbsWeight_two_uniform
    (B η₀ β η : ℝ) (hη₀ : 0 < η₀) (hβ : -B ≤ β) (hη : η₀ ≤ η) :
    ∀ᶠ n : ℕ in atTop, numberGibbsWeight β η n ≤ gibbsWeight 2 n := by
  filter_upwards
      [numberLogEnergy_tendsto_atTop.eventually_ge_atTop ((B + 2) / η₀)] with n hn
  have hL : 0 ≤ numberLogEnergy n := numberLogEnergy_nonneg n
  have hB : B + 2 ≤ η₀ * numberLogEnergy n := by
    have h := (div_le_iff₀ hη₀).mp hn
    simpa [mul_comm] using h
  have hlin0 : 2 - β ≤ B + 2 := by
    linarith
  have hlin1 : η₀ * numberLogEnergy n ≤ η * numberLogEnergy n := by
    exact mul_le_mul_of_nonneg_right hη hL
  have hlinear : 2 - β ≤ η * numberLogEnergy n :=
    hlin0.trans (hB.trans hlin1)
  have hquad : (2 - β) * numberLogEnergy n ≤
      η * (numberLogEnergy n) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hlinear hL
    nlinarith
  calc
    numberGibbsWeight β η n
        ≤ Real.exp (-2 * numberLogEnergy n) := by
          apply Real.exp_le_exp.mpr
          change -β * numberLogEnergy n - η * numberLogEnergy n ^ 2 ≤
            -2 * numberLogEnergy n
          nlinarith [hquad]
    _ = gibbsWeight 2 n := exp_zeta_eq_gibbsWeight 2 n

/-- The same compact-parameter tail works after multiplying by any fixed
logarithmic derivative factor.  This is the direct Weierstrass/M-test input for
termwise differentiation of the two-parameter partition sum: the derivatives
only change the power of `log (n+1)`, while the common exponent-`2` envelope is
independent of `(β,η)` inside the region. -/
lemma eventually_numberGibbs_moment_le_gibbs_moment_two_uniform
    (B η₀ β η : ℝ) (r : ℕ)
    (hη₀ : 0 < η₀) (hβ : -B ≤ β) (hη : η₀ ≤ η) :
    ∀ᶠ n : ℕ in atTop,
      numberGibbsWeight β η n * numberLogEnergy n ^ r ≤
        gibbsWeight 2 n * logEnergy n ^ r := by
  filter_upwards
      [eventually_numberGibbsWeight_le_gibbsWeight_two_uniform
        B η₀ β η hη₀ hβ hη] with n hn
  have hp : 0 ≤ numberLogEnergy n ^ r :=
    pow_nonneg (numberLogEnergy_nonneg n) r
  have hm := mul_le_mul_of_nonneg_right hn hp
  simpa [numberLogEnergy, logEnergy] using hm

/-- Any fixed logarithmic moment of the quadratically confined family is
summable once the corresponding exponent-`2` zeta moment is summable. -/
lemma summable_numberGibbs_moment_of_quadratic
    (β η : ℝ) (r : ℕ) (hη : 0 < η)
    (hz2 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ r)) :
    Summable (fun n : ℕ =>
      numberGibbsWeight β η n * numberLogEnergy n ^ r) := by
  apply hz2.of_norm_bounded_eventually_nat
  filter_upwards [eventually_numberGibbsWeight_le_gibbsWeight_two β η hη] with n hn
  have hp : 0 ≤ numberLogEnergy n ^ r :=
    pow_nonneg (numberLogEnergy_nonneg n) r
  have hm := mul_le_mul_of_nonneg_right hn hp
  have hw : 0 ≤ numberGibbsWeight β η n := numberGibbsWeight_nonneg β η n
  have hL : 0 ≤ numberLogEnergy n := numberLogEnergy_nonneg n
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := by
    simpa [numberLogEnergy] using hL
  simpa [Real.norm_eq_abs, abs_of_nonneg hw, numberLogEnergy, logEnergy,
    abs_of_nonneg hlog] using hm

/-- For every real `β` and every strictly positive quadratic confinement
parameter `η`, the infinite mass-aware two-parameter number-Gibbs Fisher
numerator is strictly positive, with no remaining summability hypotheses. -/
theorem numberGibbs_fisherNumerator_infinite_pos_of_eta_pos
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    0 < fisherNumerator
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 0)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 1)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 2)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 3)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 4) := by
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz0 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 0) := by
    simpa using summable_gibbsWeight htwo
  have hz1 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 1) := by
    simpa using summable_gibbsWeight_mul_logEnergy htwo
  have hz2 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 2) :=
    summable_gibbsWeight_mul_logEnergy_sq htwo
  have hz3 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 3) :=
    summable_gibbsWeight_mul_logEnergy_cube htwo
  have hz4 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 4) :=
    summable_gibbsWeight_mul_logEnergy_fourth htwo
  apply numberGibbs_fisherNumerator_infinite_pos β η
  · exact summable_numberGibbs_moment_of_quadratic β η 0 hη hz0
  · exact summable_numberGibbs_moment_of_quadratic β η 1 hη hz1
  · exact summable_numberGibbs_moment_of_quadratic β η 2 hη hz2
  · exact summable_numberGibbs_moment_of_quadratic β η 3 hη hz3
  · exact summable_numberGibbs_moment_of_quadratic β η 4 hη hz4

end GppNumberGibbsQuadraticConfinement

#print axioms GppNumberGibbsQuadraticConfinement.eventually_numberGibbsWeight_le_gibbsWeight_two_uniform
#print axioms GppNumberGibbsQuadraticConfinement.eventually_numberGibbs_moment_le_gibbs_moment_two_uniform
#print axioms GppNumberGibbsQuadraticConfinement.numberGibbs_fisherNumerator_infinite_pos_of_eta_pos
