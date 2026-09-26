import GppVerify.RiemannHypothesis.SechFourthIntegral

/-!
# The `mu^2` bubble radial shell

For a D-dimensional two-particle cut with `mu = M/(2 cosh r)`, the combination of
one `mu^2` numerator and two-body phase space gives the universal radial shape

  `tanh r / cosh^2 r`.

This file proves its exact half-line normalization

  `∫_0^∞ tanh r / cosh^2 r dr = 1/2`

from the explicit antiderivative `tanh(r)^2 / 2`.
-/

namespace GppMu2BubbleRadial

open Filter MeasureTheory
open GppSechIntegral

/-- Antiderivative of the bubble radial shell. -/
noncomputable def bubbleAntideriv (r : ℝ) : ℝ := Real.tanh r ^ 2 / 2

/-- The derivative of `tanh(r)^2 / 2` is `tanh r / cosh^2 r`. -/
theorem hasDerivAt_bubbleAntideriv (r : ℝ) :
    HasDerivAt bubbleAntideriv (Real.tanh r / Real.cosh r ^ 2) r := by
  have h := (hasDerivAt_tanh' r).pow 2 |>.div_const 2
  convert h using 1
  · simp [bubbleAntideriv]
  · rw [one_div_cosh_sq]
    ring

/-- The bubble antiderivative vanishes at threshold. -/
theorem bubbleAntideriv_zero : bubbleAntideriv 0 = 0 := by
  simp [bubbleAntideriv]

/-- `1/cosh^2 r -> 0` at the massless boundary. -/
theorem tendsto_inv_cosh_sq_zero :
    Tendsto (fun r : ℝ => 1 / Real.cosh r ^ 2) atTop (nhds 0) := by
  have h2r : Tendsto (fun r : ℝ => 2 * r) atTop atTop :=
    Tendsto.const_mul_atTop two_pos tendsto_id
  have hexp : Tendsto (fun r : ℝ => Real.exp (-(2 * r))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h2r
  have hupper : Tendsto (fun r : ℝ => 4 * Real.exp (-(2 * r))) atTop (nhds 0) := by
    simpa only [mul_zero] using hexp.const_mul (4 : ℝ)
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun r => by positivity)
    (Filter.Eventually.of_forall fun r => one_div_cosh_sq_le r)
    hupper

/-- `tanh(r)^2 -> 1` at the massless boundary. -/
theorem tendsto_tanh_sq_one :
    Tendsto (fun r : ℝ => Real.tanh r ^ 2) atTop (nhds 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub
    tendsto_inv_cosh_sq_zero
  have heq : ∀ r : ℝ, 1 - 1 / Real.cosh r ^ 2 = Real.tanh r ^ 2 := by
    intro r
    rw [one_div_cosh_sq]
    ring
  simpa only [sub_zero] using (tendsto_congr heq).mp h

/-- The bubble antiderivative tends to `1/2`. -/
theorem tendsto_bubbleAntideriv_half :
    Tendsto bubbleAntideriv atTop (nhds (1 / 2 : ℝ)) := by
  have h := tendsto_tanh_sq_one.div_const (2 : ℝ)
  simpa [bubbleAntideriv] using h

/-- The shell is nonnegative above threshold. -/
theorem bubbleShell_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ Real.tanh r / Real.cosh r ^ 2 := by
  have hsinh : 0 ≤ Real.sinh r := by
    rw [Real.sinh_eq]
    have h := Real.exp_le_exp.mpr (by linarith : -r ≤ r)
    linarith
  have htanh : 0 ≤ Real.tanh r := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg hsinh (Real.cosh_pos r).le
  exact div_nonneg htanh (sq_nonneg _)

/-- **Exact `mu^2` bubble shell normalization**:
`∫_0^∞ tanh r sech^2 r dr = 1/2`. -/
theorem integral_bubbleShell :
    ∫ r in Set.Ioi (0 : ℝ), Real.tanh r / Real.cosh r ^ 2 = 1 / 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    ((hasDerivAt_bubbleAntideriv 0).continuousAt.continuousWithinAt)
    (fun r _ => hasDerivAt_bubbleAntideriv r)
    (fun r hr => bubbleShell_nonneg hr)
    tendsto_bubbleAntideriv_half
  simpa [bubbleAntideriv_zero] using h

end GppMu2BubbleRadial

#print axioms GppMu2BubbleRadial.integral_bubbleShell
