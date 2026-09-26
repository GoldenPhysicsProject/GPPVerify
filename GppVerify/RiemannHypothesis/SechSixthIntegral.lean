import GppVerify.RiemannHypothesis.SechFourthIntegral
import Mathlib.Tactic

/-!
# The half-line sech-sixth integral

This is the elementary hyperbolic integral needed in the Parseval reduction of
the two-variable Wiener-Hopf chamber convolution.
-/

namespace GppSechSixthIntegral

open Filter MeasureTheory
open GppSechIntegral

/-- Polynomial antiderivative of `sech^6`. -/
noncomputable def sechSixthAntideriv (x : ℝ) : ℝ :=
  Real.tanh x - (2 / 3 : ℝ) * Real.tanh x ^ 3 +
    (1 / 5 : ℝ) * Real.tanh x ^ 5

/-- Exact exponential form of `tanh`, convenient for its limit at `+∞`. -/
theorem tanh_eq_exp_ratio (x : ℝ) :
    Real.tanh x =
      (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) := by
  have hsplit : Real.exp (-x) =
      Real.exp x * Real.exp (-(2 * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, hsplit]
  have hd : Real.exp x + Real.exp x * Real.exp (-(2 * x)) ≠ 0 := by
    positivity
  field_simp [hd]
  ring

/-- `tanh x -> 1` as `x -> +∞`. -/
theorem tendsto_tanh_one : Tendsto Real.tanh atTop (nhds 1) := by
  rw [tendsto_congr tanh_eq_exp_ratio]
  have h2x : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
    Tendsto.const_mul_atTop two_pos tendsto_id
  have he : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h2x
  have hn : Tendsto (fun x : ℝ => 1 - Real.exp (-(2 * x))) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub he
  have hd : Tendsto (fun x : ℝ => 1 + Real.exp (-(2 * x))) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add he
  simpa using hn.div hd one_ne_zero

/-- The antiderivative tends to `8/15`. -/
theorem tendsto_sechSixthAntideriv :
    Tendsto sechSixthAntideriv atTop (nhds (8 / 15 : ℝ)) := by
  have ht := tendsto_tanh_one
  have h := ht.sub ((ht.pow 3).const_mul (2 / 3 : ℝ)) |>.add
    ((ht.pow 5).const_mul (1 / 5 : ℝ))
  convert h using 1 <;> norm_num [sechSixthAntideriv]

/-- The derivative of the polynomial antiderivative is exactly `1/cosh^6`. -/
theorem hasDerivAt_sechSixthAntideriv (x : ℝ) :
    HasDerivAt sechSixthAntideriv (1 / Real.cosh x ^ 6) x := by
  have ht := hasDerivAt_tanh' x
  have h := ht.sub ((ht.pow 3).const_mul (2 / 3 : ℝ)) |>.add
    ((ht.pow 5).const_mul (1 / 5 : ℝ))
  convert h using 1
  · unfold sechSixthAntideriv
  · rw [show Real.cosh x ^ 6 = (Real.cosh x ^ 2) ^ 3 by ring]
    rw [show 1 / (Real.cosh x ^ 2) ^ 3 = (1 / Real.cosh x ^ 2) ^ 3 by field_simp]
    rw [one_div_cosh_sq]
    ring

/-- The antiderivative vanishes at the origin. -/
theorem sechSixthAntideriv_zero : sechSixthAntideriv 0 = 0 := by
  simp [sechSixthAntideriv]

/-- **Exact half-line integral** `∫_0^∞ sech^6 u du = 8/15`. -/
theorem integral_one_div_cosh_sixth :
    ∫ x in Set.Ioi (0 : ℝ), 1 / Real.cosh x ^ 6 = (8 / 15 : ℝ) := by
  have hcont : ContinuousWithinAt sechSixthAntideriv (Set.Ici 0) 0 :=
    (hasDerivAt_sechSixthAntideriv 0).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt sechSixthAntideriv (1 / Real.cosh x ^ 6) x :=
    fun x _ => hasDerivAt_sechSixthAntideriv x
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ 1 / Real.cosh x ^ 6 := by
    intro x hx
    positivity
  have h := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos
    tendsto_sechSixthAntideriv
  simpa [sechSixthAntideriv_zero] using h

end GppSechSixthIntegral

#print axioms GppSechSixthIntegral.integral_one_div_cosh_sixth
