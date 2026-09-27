import GppVerify.RiemannHypothesis.NumberGibbsQuadraticMomentDerivatives
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
# Higher countable derivatives of confined Gibbs moments

Extends the existing `M1`/`M2` derivative layer to `M3` and `M4`.  These are the
remaining raw-moment derivatives needed for the third response tensor of the
quadratically confined two-parameter number gas.
-/

namespace GppNumberGibbsQuadraticHigherMomentDerivatives

open Set
open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticGlobalEnvelope
open GppNumberGibbsQuadraticTermDerivatives
open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticConfinement
open GppNumberGibbsQuadraticCurvatureSummability
open GppZetaGibbsSummability

private lemma numberLogEnergy_nonneg_local (n : ℕ) : 0 ≤ numberLogEnergy n := by
  unfold numberLogEnergy
  apply Real.log_nonneg
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

/-- `∂β M3 = -M4` throughout the confined region `η > 0`. -/
theorem hasDerivAt_M3_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun b : ℝ => M3 b η) (-M4 β η) β := by
  let B : ℝ := |β| + 1
  let U : Set ℝ := Set.Ioo (β - 1) (β + 1)
  let C : ℝ := Real.exp ((B + 2) ^ 2 / (4 * η))
  let g : ℕ → ℝ → ℝ := fun n b => numberGibbsWeight b η n * numberLogEnergy n ^ 3
  let g' : ℕ → ℝ → ℝ := fun n b => -(numberGibbsWeight b η n * numberLogEnergy n ^ 4)
  let d : ℕ → ℝ := fun n => C * (gibbsWeight 2 n * logEnergy n ^ 4)
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz3 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 3) :=
    summable_gibbsWeight_mul_logEnergy_cube htwo
  have hz4 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 4) :=
    summable_gibbsWeight_mul_logEnergy_fourth htwo
  have hd : Summable d := by
    simpa [d, C] using summable_global_derivative_envelope B η 4 hz4
  have hderiv : ∀ n b, b ∈ U → HasDerivAt (g n) (g' n b) b := by
    intro n b hb
    have h := (numberGibbsWeight_hasDerivAt_beta b η n).mul_const (numberLogEnergy n ^ 3)
    convert h using 1 <;> simp [g, g'] <;> ring
  have hbound : ∀ n b, b ∈ U → ‖g' n b‖ ≤ d n := by
    intro n b hb
    have hβlower : -B ≤ b := by
      calc
        -B = -(|β| + 1) := by rfl
        _ ≤ β - 1 := by linarith [neg_abs_le β]
        _ ≤ b := le_of_lt hb.1
    have henv := numberGibbs_moment_le_const_mul_gibbs_moment_two_uniform
      B η b η 4 hη hβlower le_rfl n
    have hw0 : 0 ≤ numberGibbsWeight b η n := numberGibbsWeight_nonneg b η n
    have hL0 : 0 ≤ numberLogEnergy n ^ 4 := pow_nonneg (numberLogEnergy_nonneg_local n) 4
    dsimp [g']
    rw [abs_neg, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hL0]
    simpa [d, C, numberLogEnergy, logEnergy] using henv
  have hbase_mem : β ∈ U := by dsimp [U]; constructor <;> linarith
  have hbase : Summable (fun n : ℕ => g n β) := by
    simpa [g] using (summable_numberGibbs_moment_of_quadratic β η 3 hη hz3)
  have H := hasDerivAt_tsum_of_isPreconnected
    hd isOpen_Ioo isPreconnected_Ioo hderiv hbound hbase_mem hbase hbase_mem
  have H' : HasDerivAt (fun b : ℝ => M3 b η) (∑' n : ℕ, g' n β) β := by
    simpa [M3, g] using H
  convert H' using 1
  unfold M4
  rw [← tsum_neg]

/-- `∂η M3 = -M5` throughout the confined region `η > 0`. -/
theorem hasDerivAt_M3_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun e : ℝ => M3 β e) (-M5 β η) η := by
  let B : ℝ := |β|
  let η₀ : ℝ := η / 2
  let U : Set ℝ := Set.Ioo (η / 2) (3 * η / 2)
  let C : ℝ := Real.exp ((B + 2) ^ 2 / (4 * η₀))
  let g : ℕ → ℝ → ℝ := fun n e => numberGibbsWeight β e n * numberLogEnergy n ^ 3
  let g' : ℕ → ℝ → ℝ := fun n e => -(numberGibbsWeight β e n * numberLogEnergy n ^ 5)
  let d : ℕ → ℝ := fun n => C * (gibbsWeight 2 n * logEnergy n ^ 5)
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz3 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 3) :=
    summable_gibbsWeight_mul_logEnergy_cube htwo
  have hz5 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 5) :=
    summable_gibbsWeight_mul_logEnergy_fifth htwo
  have hη₀ : 0 < η₀ := by dsimp [η₀]; linarith
  have hd : Summable d := by
    simpa [d, C] using summable_global_derivative_envelope B η₀ 5 hz5
  have hderiv : ∀ n e, e ∈ U → HasDerivAt (g n) (g' n e) e := by
    intro n e he
    have h := (numberGibbsWeight_hasDerivAt_eta β e n).mul_const (numberLogEnergy n ^ 3)
    convert h using 1 <;> simp [g, g'] <;> ring
  have hbound : ∀ n e, e ∈ U → ‖g' n e‖ ≤ d n := by
    intro n e he
    have hβlower : -B ≤ β := by dsimp [B]; exact neg_abs_le β
    have hηlower : η₀ ≤ e := by dsimp [η₀, U] at he ⊢; exact le_of_lt he.1
    have henv := numberGibbs_moment_le_const_mul_gibbs_moment_two_uniform
      B η₀ β e 5 hη₀ hβlower hηlower n
    have hw0 : 0 ≤ numberGibbsWeight β e n := numberGibbsWeight_nonneg β e n
    have hL0 : 0 ≤ numberLogEnergy n ^ 5 := pow_nonneg (numberLogEnergy_nonneg_local n) 5
    dsimp [g']
    rw [abs_neg, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hL0]
    simpa [d, C, numberLogEnergy, logEnergy] using henv
  have hbase_mem : η ∈ U := by dsimp [U]; constructor <;> linarith
  have hbase : Summable (fun n : ℕ => g n η) := by
    simpa [g] using (summable_numberGibbs_moment_of_quadratic β η 3 hη hz3)
  have H := hasDerivAt_tsum_of_isPreconnected
    hd isOpen_Ioo isPreconnected_Ioo hderiv hbound hbase_mem hbase hbase_mem
  have H' : HasDerivAt (fun e : ℝ => M3 β e) (∑' n : ℕ, g' n η) η := by
    simpa [M3, g] using H
  convert H' using 1
  unfold M5
  rw [← tsum_neg]

/-- `∂β M4 = -M5` throughout the confined region `η > 0`. -/
theorem hasDerivAt_M4_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun b : ℝ => M4 b η) (-M5 β η) β := by
  let B : ℝ := |β| + 1
  let U : Set ℝ := Set.Ioo (β - 1) (β + 1)
  let C : ℝ := Real.exp ((B + 2) ^ 2 / (4 * η))
  let g : ℕ → ℝ → ℝ := fun n b => numberGibbsWeight b η n * numberLogEnergy n ^ 4
  let g' : ℕ → ℝ → ℝ := fun n b => -(numberGibbsWeight b η n * numberLogEnergy n ^ 5)
  let d : ℕ → ℝ := fun n => C * (gibbsWeight 2 n * logEnergy n ^ 5)
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz4 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 4) :=
    summable_gibbsWeight_mul_logEnergy_fourth htwo
  have hz5 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 5) :=
    summable_gibbsWeight_mul_logEnergy_fifth htwo
  have hd : Summable d := by
    simpa [d, C] using summable_global_derivative_envelope B η 5 hz5
  have hderiv : ∀ n b, b ∈ U → HasDerivAt (g n) (g' n b) b := by
    intro n b hb
    have h := (numberGibbsWeight_hasDerivAt_beta b η n).mul_const (numberLogEnergy n ^ 4)
    convert h using 1 <;> simp [g, g'] <;> ring
  have hbound : ∀ n b, b ∈ U → ‖g' n b‖ ≤ d n := by
    intro n b hb
    have hβlower : -B ≤ b := by
      calc
        -B = -(|β| + 1) := by rfl
        _ ≤ β - 1 := by linarith [neg_abs_le β]
        _ ≤ b := le_of_lt hb.1
    have henv := numberGibbs_moment_le_const_mul_gibbs_moment_two_uniform
      B η b η 5 hη hβlower le_rfl n
    have hw0 : 0 ≤ numberGibbsWeight b η n := numberGibbsWeight_nonneg b η n
    have hL0 : 0 ≤ numberLogEnergy n ^ 5 := pow_nonneg (numberLogEnergy_nonneg_local n) 5
    dsimp [g']
    rw [abs_neg, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hL0]
    simpa [d, C, numberLogEnergy, logEnergy] using henv
  have hbase_mem : β ∈ U := by dsimp [U]; constructor <;> linarith
  have hbase : Summable (fun n : ℕ => g n β) := by
    simpa [g] using (summable_numberGibbs_moment_of_quadratic β η 4 hη hz4)
  have H := hasDerivAt_tsum_of_isPreconnected
    hd isOpen_Ioo isPreconnected_Ioo hderiv hbound hbase_mem hbase hbase_mem
  have H' : HasDerivAt (fun b : ℝ => M4 b η) (∑' n : ℕ, g' n β) β := by
    simpa [M4, g] using H
  convert H' using 1
  unfold M5
  rw [← tsum_neg]

/-- `∂η M4 = -M6` throughout the confined region `η > 0`. -/
theorem hasDerivAt_M4_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun e : ℝ => M4 β e) (-M6 β η) η := by
  let B : ℝ := |β|
  let η₀ : ℝ := η / 2
  let U : Set ℝ := Set.Ioo (η / 2) (3 * η / 2)
  let C : ℝ := Real.exp ((B + 2) ^ 2 / (4 * η₀))
  let g : ℕ → ℝ → ℝ := fun n e => numberGibbsWeight β e n * numberLogEnergy n ^ 4
  let g' : ℕ → ℝ → ℝ := fun n e => -(numberGibbsWeight β e n * numberLogEnergy n ^ 6)
  let d : ℕ → ℝ := fun n => C * (gibbsWeight 2 n * logEnergy n ^ 6)
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz4 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 4) :=
    summable_gibbsWeight_mul_logEnergy_fourth htwo
  have hz6 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 6) :=
    summable_gibbsWeight_mul_logEnergy_sixth htwo
  have hη₀ : 0 < η₀ := by dsimp [η₀]; linarith
  have hd : Summable d := by
    simpa [d, C] using summable_global_derivative_envelope B η₀ 6 hz6
  have hderiv : ∀ n e, e ∈ U → HasDerivAt (g n) (g' n e) e := by
    intro n e he
    have h := (numberGibbsWeight_hasDerivAt_eta β e n).mul_const (numberLogEnergy n ^ 4)
    convert h using 1 <;> simp [g, g'] <;> ring
  have hbound : ∀ n e, e ∈ U → ‖g' n e‖ ≤ d n := by
    intro n e he
    have hβlower : -B ≤ β := by dsimp [B]; exact neg_abs_le β
    have hηlower : η₀ ≤ e := by dsimp [η₀, U] at he ⊢; exact le_of_lt he.1
    have henv := numberGibbs_moment_le_const_mul_gibbs_moment_two_uniform
      B η₀ β e 6 hη₀ hβlower hηlower n
    have hw0 : 0 ≤ numberGibbsWeight β e n := numberGibbsWeight_nonneg β e n
    have hL0 : 0 ≤ numberLogEnergy n ^ 6 := pow_nonneg (numberLogEnergy_nonneg_local n) 6
    dsimp [g']
    rw [abs_neg, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hL0]
    simpa [d, C, numberLogEnergy, logEnergy] using henv
  have hbase_mem : η ∈ U := by dsimp [U]; constructor <;> linarith
  have hbase : Summable (fun n : ℕ => g n η) := by
    simpa [g] using (summable_numberGibbs_moment_of_quadratic β η 4 hη hz4)
  have H := hasDerivAt_tsum_of_isPreconnected
    hd isOpen_Ioo isPreconnected_Ioo hderiv hbound hbase_mem hbase hbase_mem
  have H' : HasDerivAt (fun e : ℝ => M4 β e) (∑' n : ℕ, g' n η) η := by
    simpa [M4, g] using H
  convert H' using 1
  unfold M6
  rw [← tsum_neg]

end GppNumberGibbsQuadraticHigherMomentDerivatives

#print axioms GppNumberGibbsQuadraticHigherMomentDerivatives.hasDerivAt_M3_beta
#print axioms GppNumberGibbsQuadraticHigherMomentDerivatives.hasDerivAt_M3_eta
#print axioms GppNumberGibbsQuadraticHigherMomentDerivatives.hasDerivAt_M4_beta
#print axioms GppNumberGibbsQuadraticHigherMomentDerivatives.hasDerivAt_M4_eta
