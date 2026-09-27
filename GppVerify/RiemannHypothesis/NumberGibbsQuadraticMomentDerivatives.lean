import GppVerify.RiemannHypothesis.NumberGibbsQuadraticGlobalEnvelope
import GppVerify.RiemannHypothesis.NumberGibbsQuadraticTermDerivatives
import GppVerify.RiemannHypothesis.NumberGibbsQuadraticThermodynamics
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
# Countable derivatives of the confined Gibbs moments

The same global quadratic-confinement envelope used for the partition function
also controls the first two raw moments under differentiation. This promotes
the exact termwise `L^2`, `L^3`, and `L^4` derivatives to the actual countable
moment sums and supplies the second-derivative data for the Massieu Hessian.
-/

namespace GppNumberGibbsQuadraticMomentDerivatives

open Set
open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticGlobalEnvelope
open GppNumberGibbsQuadraticTermDerivatives
open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticConfinement
open GppZetaGibbsSummability

private lemma numberLogEnergy_nonneg_local (n : ℕ) : 0 ≤ numberLogEnergy n := by
  unfold numberLogEnergy
  apply Real.log_nonneg
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

/-- `∂β M1 = -M2` throughout the confined region `η > 0`. -/
theorem hasDerivAt_M1_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun b : ℝ => M1 b η) (-M2 β η) β := by
  let B : ℝ := |β| + 1
  let U : Set ℝ := Set.Ioo (β - 1) (β + 1)
  let C : ℝ := Real.exp ((B + 2) ^ 2 / (4 * η))
  let g : ℕ → ℝ → ℝ := fun n b => numberGibbsWeight b η n * numberLogEnergy n
  let g' : ℕ → ℝ → ℝ := fun n b => -(numberGibbsWeight b η n * numberLogEnergy n ^ 2)
  let d : ℕ → ℝ := fun n => C * (gibbsWeight 2 n * logEnergy n ^ 2)
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz1 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 1) := by
    simpa [pow_one] using summable_gibbsWeight_mul_logEnergy htwo
  have hz2 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 2) :=
    summable_gibbsWeight_mul_logEnergy_sq htwo
  have hd : Summable d := by
    simpa [d, C] using summable_global_derivative_envelope B η 2 hz2
  have hderiv : ∀ n b, b ∈ U → HasDerivAt (g n) (g' n b) b := by
    intro n b hb
    have h := (numberGibbsWeight_hasDerivAt_beta b η n).mul_const (numberLogEnergy n)
    convert h using 1 <;> simp [g, g'] <;> ring
  have hbound : ∀ n b, b ∈ U → ‖g' n b‖ ≤ d n := by
    intro n b hb
    have hβlower : -B ≤ b := by
      calc
        -B = -(|β| + 1) := by rfl
        _ ≤ β - 1 := by linarith [neg_abs_le β]
        _ ≤ b := le_of_lt hb.1
    have henv := numberGibbs_moment_le_const_mul_gibbs_moment_two_uniform
      B η b η 2 hη hβlower le_rfl n
    have hw0 : 0 ≤ numberGibbsWeight b η n := numberGibbsWeight_nonneg b η n
    have hL0 : 0 ≤ numberLogEnergy n ^ 2 := sq_nonneg _
    dsimp [g']
    rw [abs_neg, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hL0]
    simpa [d, C, numberLogEnergy, logEnergy] using henv
  have hbase_mem : β ∈ U := by
    dsimp [U]
    constructor <;> linarith
  have hbase : Summable (fun n : ℕ => g n β) := by
    simpa [g, pow_one] using
      (summable_numberGibbs_moment_of_quadratic β η 1 hη hz1)
  have H := hasDerivAt_tsum_of_isPreconnected
    hd isOpen_Ioo isPreconnected_Ioo hderiv hbound hbase_mem hbase hbase_mem
  have H' : HasDerivAt (fun b : ℝ => M1 b η) (∑' n : ℕ, g' n β) β := by
    simpa [M1, g] using H
  convert H' using 1
  unfold M2
  rw [← tsum_neg]

/-- `∂η M1 = -M3` throughout the confined region `η > 0`. -/
theorem hasDerivAt_M1_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun e : ℝ => M1 β e) (-M3 β η) η := by
  let B : ℝ := |β|
  let η₀ : ℝ := η / 2
  let U : Set ℝ := Set.Ioo (η / 2) (3 * η / 2)
  let C : ℝ := Real.exp ((B + 2) ^ 2 / (4 * η₀))
  let g : ℕ → ℝ → ℝ := fun n e => numberGibbsWeight β e n * numberLogEnergy n
  let g' : ℕ → ℝ → ℝ := fun n e => -(numberGibbsWeight β e n * numberLogEnergy n ^ 3)
  let d : ℕ → ℝ := fun n => C * (gibbsWeight 2 n * logEnergy n ^ 3)
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz1 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 1) := by
    simpa [pow_one] using summable_gibbsWeight_mul_logEnergy htwo
  have hz3 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 3) :=
    summable_gibbsWeight_mul_logEnergy_cube htwo
  have hη₀ : 0 < η₀ := by dsimp [η₀]; linarith
  have hd : Summable d := by
    simpa [d, C] using summable_global_derivative_envelope B η₀ 3 hz3
  have hderiv : ∀ n e, e ∈ U → HasDerivAt (g n) (g' n e) e := by
    intro n e he
    have h := (numberGibbsWeight_hasDerivAt_eta β e n).mul_const (numberLogEnergy n)
    convert h using 1 <;> simp [g, g'] <;> ring
  have hbound : ∀ n e, e ∈ U → ‖g' n e‖ ≤ d n := by
    intro n e he
    have hβlower : -B ≤ β := by dsimp [B]; exact neg_abs_le β
    have hηlower : η₀ ≤ e := by
      dsimp [η₀, U] at he ⊢
      exact le_of_lt he.1
    have henv := numberGibbs_moment_le_const_mul_gibbs_moment_two_uniform
      B η₀ β e 3 hη₀ hβlower hηlower n
    have hw0 : 0 ≤ numberGibbsWeight β e n := numberGibbsWeight_nonneg β e n
    have hL0 : 0 ≤ numberLogEnergy n ^ 3 := pow_nonneg (numberLogEnergy_nonneg_local n) 3
    dsimp [g']
    rw [abs_neg, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hL0]
    simpa [d, C, numberLogEnergy, logEnergy] using henv
  have hbase_mem : η ∈ U := by
    dsimp [U]
    constructor <;> linarith
  have hbase : Summable (fun n : ℕ => g n η) := by
    simpa [g, pow_one] using
      (summable_numberGibbs_moment_of_quadratic β η 1 hη hz1)
  have H := hasDerivAt_tsum_of_isPreconnected
    hd isOpen_Ioo isPreconnected_Ioo hderiv hbound hbase_mem hbase hbase_mem
  have H' : HasDerivAt (fun e : ℝ => M1 β e) (∑' n : ℕ, g' n η) η := by
    simpa [M1, g] using H
  convert H' using 1
  unfold M3
  rw [← tsum_neg]

/-- `∂β M2 = -M3` throughout the confined region `η > 0`. -/
theorem hasDerivAt_M2_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun b : ℝ => M2 b η) (-M3 β η) β := by
  let B : ℝ := |β| + 1
  let U : Set ℝ := Set.Ioo (β - 1) (β + 1)
  let C : ℝ := Real.exp ((B + 2) ^ 2 / (4 * η))
  let g : ℕ → ℝ → ℝ := fun n b => numberGibbsWeight b η n * numberLogEnergy n ^ 2
  let g' : ℕ → ℝ → ℝ := fun n b => -(numberGibbsWeight b η n * numberLogEnergy n ^ 3)
  let d : ℕ → ℝ := fun n => C * (gibbsWeight 2 n * logEnergy n ^ 3)
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz2 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 2) :=
    summable_gibbsWeight_mul_logEnergy_sq htwo
  have hz3 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 3) :=
    summable_gibbsWeight_mul_logEnergy_cube htwo
  have hd : Summable d := by
    simpa [d, C] using summable_global_derivative_envelope B η 3 hz3
  have hderiv : ∀ n b, b ∈ U → HasDerivAt (g n) (g' n b) b := by
    intro n b hb
    have h := (numberGibbsWeight_hasDerivAt_beta b η n).mul_const (numberLogEnergy n ^ 2)
    convert h using 1 <;> simp [g, g'] <;> ring
  have hbound : ∀ n b, b ∈ U → ‖g' n b‖ ≤ d n := by
    intro n b hb
    have hβlower : -B ≤ b := by
      calc
        -B = -(|β| + 1) := by rfl
        _ ≤ β - 1 := by linarith [neg_abs_le β]
        _ ≤ b := le_of_lt hb.1
    have henv := numberGibbs_moment_le_const_mul_gibbs_moment_two_uniform
      B η b η 3 hη hβlower le_rfl n
    have hw0 : 0 ≤ numberGibbsWeight b η n := numberGibbsWeight_nonneg b η n
    have hL0 : 0 ≤ numberLogEnergy n ^ 3 := pow_nonneg (numberLogEnergy_nonneg_local n) 3
    dsimp [g']
    rw [abs_neg, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hL0]
    simpa [d, C, numberLogEnergy, logEnergy] using henv
  have hbase_mem : β ∈ U := by
    dsimp [U]
    constructor <;> linarith
  have hbase : Summable (fun n : ℕ => g n β) := by
    simpa [g] using
      (summable_numberGibbs_moment_of_quadratic β η 2 hη hz2)
  have H := hasDerivAt_tsum_of_isPreconnected
    hd isOpen_Ioo isPreconnected_Ioo hderiv hbound hbase_mem hbase hbase_mem
  have H' : HasDerivAt (fun b : ℝ => M2 b η) (∑' n : ℕ, g' n β) β := by
    simpa [M2, g] using H
  convert H' using 1
  unfold M3
  rw [← tsum_neg]

/-- `∂η M2 = -M4` throughout the confined region `η > 0`. -/
theorem hasDerivAt_M2_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun e : ℝ => M2 β e) (-M4 β η) η := by
  let B : ℝ := |β|
  let η₀ : ℝ := η / 2
  let U : Set ℝ := Set.Ioo (η / 2) (3 * η / 2)
  let C : ℝ := Real.exp ((B + 2) ^ 2 / (4 * η₀))
  let g : ℕ → ℝ → ℝ := fun n e => numberGibbsWeight β e n * numberLogEnergy n ^ 2
  let g' : ℕ → ℝ → ℝ := fun n e => -(numberGibbsWeight β e n * numberLogEnergy n ^ 4)
  let d : ℕ → ℝ := fun n => C * (gibbsWeight 2 n * logEnergy n ^ 4)
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz2 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 2) :=
    summable_gibbsWeight_mul_logEnergy_sq htwo
  have hz4 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 4) :=
    summable_gibbsWeight_mul_logEnergy_fourth htwo
  have hη₀ : 0 < η₀ := by dsimp [η₀]; linarith
  have hd : Summable d := by
    simpa [d, C] using summable_global_derivative_envelope B η₀ 4 hz4
  have hderiv : ∀ n e, e ∈ U → HasDerivAt (g n) (g' n e) e := by
    intro n e he
    have h := (numberGibbsWeight_hasDerivAt_eta β e n).mul_const (numberLogEnergy n ^ 2)
    convert h using 1 <;> simp [g, g'] <;> ring
  have hbound : ∀ n e, e ∈ U → ‖g' n e‖ ≤ d n := by
    intro n e he
    have hβlower : -B ≤ β := by dsimp [B]; exact neg_abs_le β
    have hηlower : η₀ ≤ e := by
      dsimp [η₀, U] at he ⊢
      exact le_of_lt he.1
    have henv := numberGibbs_moment_le_const_mul_gibbs_moment_two_uniform
      B η₀ β e 4 hη₀ hβlower hηlower n
    have hw0 : 0 ≤ numberGibbsWeight β e n := numberGibbsWeight_nonneg β e n
    have hL0 : 0 ≤ numberLogEnergy n ^ 4 := pow_nonneg (numberLogEnergy_nonneg_local n) 4
    dsimp [g']
    rw [abs_neg, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hL0]
    simpa [d, C, numberLogEnergy, logEnergy] using henv
  have hbase_mem : η ∈ U := by
    dsimp [U]
    constructor <;> linarith
  have hbase : Summable (fun n : ℕ => g n η) := by
    simpa [g] using
      (summable_numberGibbs_moment_of_quadratic β η 2 hη hz2)
  have H := hasDerivAt_tsum_of_isPreconnected
    hd isOpen_Ioo isPreconnected_Ioo hderiv hbound hbase_mem hbase hbase_mem
  have H' : HasDerivAt (fun e : ℝ => M2 β e) (∑' n : ℕ, g' n η) η := by
    simpa [M2, g] using H
  convert H' using 1
  unfold M4
  rw [← tsum_neg]

end GppNumberGibbsQuadraticMomentDerivatives

#print axioms GppNumberGibbsQuadraticMomentDerivatives.hasDerivAt_M1_beta
#print axioms GppNumberGibbsQuadraticMomentDerivatives.hasDerivAt_M1_eta
#print axioms GppNumberGibbsQuadraticMomentDerivatives.hasDerivAt_M2_beta
#print axioms GppNumberGibbsQuadraticMomentDerivatives.hasDerivAt_M2_eta