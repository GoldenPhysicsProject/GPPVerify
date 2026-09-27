import GppVerify.RiemannHypothesis.NumberGibbsQuadraticConfinement
import Mathlib.Tactic

/-!
# Global compact-parameter envelope for quadratic number-Gibbs weights

The earlier confinement theorem gives an eventual exponent-2 zeta envelope.
Completing the square strengthens this to an all-index envelope on every region
`β ≥ -B`, `η ≥ η₀ > 0`:

  w_{β,η}(n) ≤ exp((B+2)^2/(4η₀)) w_2(n).

The same constant works after multiplying by every fixed logarithmic moment.
This is the direct all-index majorant required by Mathlib's termwise-derivative
`tsum` theorem, avoiding a separate finite-exception splice.
-/

namespace GppNumberGibbsQuadraticGlobalEnvelope

open GppNumberGibbsQuadraticConfinement
open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsTwoParameterZetaWedge
open GppZetaGibbsSummability
open GppCountableFisherMomentLimit

/-- Completing the square gives the global exponent bound behind the uniform
number-Gibbs M-test. -/
lemma quadratic_linear_global_bound
    {B η₀ L : ℝ} (hη₀ : 0 < η₀) :
    (B + 2) * L - η₀ * L ^ 2 ≤ (B + 2) ^ 2 / (4 * η₀) := by
  have hden : 0 < 4 * η₀ := by positivity
  apply (le_div_iff₀ hden).2
  have hsquare : 0 ≤ (2 * η₀ * L - (B + 2)) ^ 2 := sq_nonneg _
  nlinarith

/-- Uniform all-index domination by the fixed exponent-2 zeta weight. -/
lemma numberGibbsWeight_le_const_mul_gibbsWeight_two_uniform
    (B η₀ β η : ℝ) (hη₀ : 0 < η₀) (hβ : -B ≤ β) (hη : η₀ ≤ η) :
    ∀ n : ℕ,
      numberGibbsWeight β η n ≤
        Real.exp ((B + 2) ^ 2 / (4 * η₀)) * gibbsWeight 2 n := by
  intro n
  let L : ℝ := numberLogEnergy n
  have hL : 0 ≤ L := by
    simpa [L] using numberLogEnergy_nonneg n
  have hβL : -β * L ≤ B * L := by
    have hb : -β ≤ B := by linarith
    exact mul_le_mul_of_nonneg_right hb hL
  have hηL : -η * L ^ 2 ≤ -η₀ * L ^ 2 := by
    have hsq : 0 ≤ L ^ 2 := sq_nonneg L
    nlinarith
  have hquad := quadratic_linear_global_bound (B := B) (η₀ := η₀) (L := L) hη₀
  have hexp :
      -β * L - η * L ^ 2 ≤
        -2 * L + (B + 2) ^ 2 / (4 * η₀) := by
    nlinarith
  calc
    numberGibbsWeight β η n
        ≤ Real.exp (-2 * L + (B + 2) ^ 2 / (4 * η₀)) := by
          unfold numberGibbsWeight
          simpa [L, numberLogEnergy] using Real.exp_le_exp.mpr hexp
    _ = Real.exp ((B + 2) ^ 2 / (4 * η₀)) * Real.exp (-2 * L) := by
          rw [show -2 * L + (B + 2) ^ 2 / (4 * η₀) =
            (B + 2) ^ 2 / (4 * η₀) + (-2 * L) by ring]
          rw [Real.exp_add]
    _ = Real.exp ((B + 2) ^ 2 / (4 * η₀)) * gibbsWeight 2 n := by
          rw [show Real.exp (-2 * L) = gibbsWeight 2 n by
            simpa [L, numberLogEnergy] using exp_zeta_eq_gibbsWeight 2 n]

/-- The same global constant dominates every fixed logarithmic derivative
moment. -/
lemma numberGibbs_moment_le_const_mul_gibbs_moment_two_uniform
    (B η₀ β η : ℝ) (r : ℕ)
    (hη₀ : 0 < η₀) (hβ : -B ≤ β) (hη : η₀ ≤ η) :
    ∀ n : ℕ,
      numberGibbsWeight β η n * numberLogEnergy n ^ r ≤
        Real.exp ((B + 2) ^ 2 / (4 * η₀)) *
          (gibbsWeight 2 n * logEnergy n ^ r) := by
  intro n
  have hw := numberGibbsWeight_le_const_mul_gibbsWeight_two_uniform
    B η₀ β η hη₀ hβ hη n
  have hp : 0 ≤ numberLogEnergy n ^ r :=
    pow_nonneg (numberLogEnergy_nonneg n) r
  have hm := mul_le_mul_of_nonneg_right hw hp
  simpa [numberLogEnergy, logEnergy, mul_assoc] using hm

/-- Consequently any known exponent-2 logarithmic moment supplies a single
summable all-index majorant valid throughout the compact parameter region. -/
lemma summable_global_derivative_envelope
    (B η₀ : ℝ) (r : ℕ)
    (hz2 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ r)) :
    Summable (fun n : ℕ =>
      Real.exp ((B + 2) ^ 2 / (4 * η₀)) *
        (gibbsWeight 2 n * logEnergy n ^ r)) := by
  exact Summable.mul_left _ hz2

end GppNumberGibbsQuadraticGlobalEnvelope

#print axioms GppNumberGibbsQuadraticGlobalEnvelope.quadratic_linear_global_bound
#print axioms GppNumberGibbsQuadraticGlobalEnvelope.numberGibbsWeight_le_const_mul_gibbsWeight_two_uniform
#print axioms GppNumberGibbsQuadraticGlobalEnvelope.numberGibbs_moment_le_const_mul_gibbs_moment_two_uniform
#print axioms GppNumberGibbsQuadraticGlobalEnvelope.summable_global_derivative_envelope
