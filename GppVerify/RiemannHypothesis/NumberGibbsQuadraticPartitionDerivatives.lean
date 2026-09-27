import GppVerify.RiemannHypothesis.NumberGibbsQuadraticGlobalEnvelope
import GppVerify.RiemannHypothesis.NumberGibbsQuadraticTermDerivatives
import GppVerify.RiemannHypothesis.NumberGibbsQuadraticThermodynamics
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
# Countable differentiation of the quadratically confined partition function

Quadratic confinement supplies a single summable all-index envelope on a full
open neighborhood of every parameter point with `η > 0`, while each summand has
an exact derivative.  This file promotes those pointwise identities through the
countable partition sum in both thermodynamic coordinates.
-/

namespace GppNumberGibbsQuadraticPartitionDerivatives

open Set
open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticGlobalEnvelope
open GppNumberGibbsQuadraticTermDerivatives
open GppNumberGibbsQuadraticThermodynamics
open GppZetaGibbsSummability

/-- At every `η > 0`, the quadratically confined partition function is
termwise differentiable in `β`. The derivative is the absolutely convergent
sum of the exact summand derivatives. -/
theorem hasDerivAt_Z_beta_raw
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt
      (fun b : ℝ => Z b η)
      (∑' n : ℕ, numberGibbsWeight β η n * (-numberLogEnergy n)) β := by
  let B : ℝ := |β| + 1
  let U : Set ℝ := Set.Ioo (β - 1) (β + 1)
  let C : ℝ := Real.exp ((B + 2) ^ 2 / (4 * η))
  let g : ℕ → ℝ → ℝ := fun n b => numberGibbsWeight b η n
  let g' : ℕ → ℝ → ℝ := fun n b =>
    numberGibbsWeight b η n * (-numberLogEnergy n)
  let d : ℕ → ℝ := fun n => C * (gibbsWeight 2 n * logEnergy n ^ 1)

  have hz1 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 1) := by
    simpa [pow_one] using
      (summable_gibbsWeight_mul_logEnergy (β := 2) (by norm_num : (1 : ℝ) < 2))
  have hd : Summable d := by
    simpa [d, C] using
      (summable_global_derivative_envelope B η 1 hz1)

  have hderiv : ∀ n b, b ∈ U → HasDerivAt (g n) (g' n b) b := by
    intro n b hb
    simpa [g, g'] using numberGibbsWeight_hasDerivAt_beta b η n

  have hbound : ∀ n b, b ∈ U → ‖g' n b‖ ≤ d n := by
    intro n b hb
    have hβlower : -B ≤ b := by
      calc
        -B = -(|β| + 1) := by rfl
        _ ≤ β - 1 := by linarith [neg_abs_le β]
        _ ≤ b := le_of_lt hb.1
    have henv := numberGibbs_moment_le_const_mul_gibbs_moment_two_uniform
      B η b η 1 hη hβlower le_rfl n
    have hw0 : 0 ≤ numberGibbsWeight b η n := numberGibbsWeight_nonneg b η n
    have hL0 : 0 ≤ numberLogEnergy n := by
      unfold numberLogEnergy
      apply Real.log_nonneg
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    dsimp [g']
    rw [abs_mul, abs_neg, abs_of_nonneg hw0, abs_of_nonneg hL0]
    simpa [d, C, pow_one, numberLogEnergy, logEnergy] using henv

  have hbase_mem : β ∈ U := by
    dsimp [U]
    constructor <;> linarith
  have hbase : Summable (fun n : ℕ => g n β) := by
    simpa [g] using summable_numberGibbsWeight β hη

  have H := hasDerivAt_tsum_of_isPreconnected
    hd isOpen_Ioo isPreconnected_Ioo hderiv hbound hbase_mem hbase hbase_mem
  simpa [Z, g, g'] using H

/-- The inverse-temperature derivative is exactly minus the first raw
log-energy moment.  This is the thermodynamic identity `∂β Z = -M1`, now at the
actual countable partition-function level rather than only termwise. -/
theorem hasDerivAt_Z_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun b : ℝ => Z b η) (-M1 β η) β := by
  convert hasDerivAt_Z_beta_raw β hη using 1
  unfold M1
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  ring

/-- At every point in the quadratically confined domain, the partition
function is termwise differentiable in `η`.  A neighborhood bounded below by
`η/2` supplies a single exponent-2 second-moment envelope. -/
theorem hasDerivAt_Z_eta_raw
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt
      (fun e : ℝ => Z β e)
      (∑' n : ℕ, numberGibbsWeight β η n * (-(numberLogEnergy n) ^ 2)) η := by
  let B : ℝ := |β|
  let η₀ : ℝ := η / 2
  let U : Set ℝ := Set.Ioo (η / 2) (3 * η / 2)
  let C : ℝ := Real.exp ((B + 2) ^ 2 / (4 * η₀))
  let g : ℕ → ℝ → ℝ := fun n e => numberGibbsWeight β e n
  let g' : ℕ → ℝ → ℝ := fun n e =>
    numberGibbsWeight β e n * (-(numberLogEnergy n) ^ 2)
  let d : ℕ → ℝ := fun n => C * (gibbsWeight 2 n * logEnergy n ^ 2)

  have hη₀ : 0 < η₀ := by
    dsimp [η₀]
    linarith
  have hz2 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 2) := by
    simpa using
      (summable_gibbsWeight_mul_logEnergy_sq (β := 2) (by norm_num : (1 : ℝ) < 2))
  have hd : Summable d := by
    simpa [d, C] using
      (summable_global_derivative_envelope B η₀ 2 hz2)

  have hderiv : ∀ n e, e ∈ U → HasDerivAt (g n) (g' n e) e := by
    intro n e he
    simpa [g, g'] using numberGibbsWeight_hasDerivAt_eta β e n

  have hbound : ∀ n e, e ∈ U → ‖g' n e‖ ≤ d n := by
    intro n e he
    have hβlower : -B ≤ β := by
      dsimp [B]
      exact neg_abs_le β
    have hηlower : η₀ ≤ e := by
      dsimp [η₀, U] at he ⊢
      exact le_of_lt he.1
    have henv := numberGibbs_moment_le_const_mul_gibbs_moment_two_uniform
      B η₀ β e 2 hη₀ hβlower hηlower n
    have hw0 : 0 ≤ numberGibbsWeight β e n := numberGibbsWeight_nonneg β e n
    have hLsq0 : 0 ≤ numberLogEnergy n ^ 2 := sq_nonneg _
    dsimp [g']
    rw [abs_mul, abs_neg, abs_of_nonneg hw0, abs_of_nonneg hLsq0]
    simpa [d, C, numberLogEnergy, logEnergy] using henv

  have hbase_mem : η ∈ U := by
    dsimp [U]
    constructor <;> linarith
  have hbase : Summable (fun n : ℕ => g n η) := by
    simpa [g] using summable_numberGibbsWeight β hη

  have H := hasDerivAt_tsum_of_isPreconnected
    hd isOpen_Ioo isPreconnected_Ioo hderiv hbound hbase_mem hbase hbase_mem
  simpa [Z, g, g'] using H

/-- The confinement derivative is exactly minus the second raw log-energy
moment: `∂η Z = -M2`. -/
theorem hasDerivAt_Z_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun e : ℝ => Z β e) (-M2 β η) η := by
  convert hasDerivAt_Z_eta_raw β hη using 1
  unfold M2
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  ring

end GppNumberGibbsQuadraticPartitionDerivatives

#print axioms GppNumberGibbsQuadraticPartitionDerivatives.hasDerivAt_Z_beta_raw
#print axioms GppNumberGibbsQuadraticPartitionDerivatives.hasDerivAt_Z_beta
#print axioms GppNumberGibbsQuadraticPartitionDerivatives.hasDerivAt_Z_eta_raw
#print axioms GppNumberGibbsQuadraticPartitionDerivatives.hasDerivAt_Z_eta
