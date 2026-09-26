import GppVerify.CelestialHolography.SechConvolutionKernel
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Log-cosh primitive for the shifted sech convolution

This is the differential layer between the pointwise hyperbolic identity in
`SechConvolutionKernel` and the eventual whole-line improper integral.  For fixed
`lambda`, the difference of two log-cosh terms differentiates to the shifted
reciprocal-cosh product multiplied by the constant channel factor
`pi * sinh (pi * lambda)`.

The endpoint algebra is also made quantitative through the exact decomposition
`log(cosh y)=|y|-log 2+log(1+exp(-2|y|))` and the elementary remainder bound.
The final improper-integral passage is kept separate.
-/

namespace GppSechConvolutionPrimitive

open GppSechConvolutionKernel

/-- The numerator primitive whose endpoint jump produces the sech self-convolution. -/
noncomputable def logCoshDifference (lam x : ℝ) : ℝ :=
  Real.log (Real.cosh (Real.pi * x)) -
    Real.log (Real.cosh (Real.pi * (lam - x)))

/-- Exponentially small correction in the exact log-cosh decomposition. -/
noncomputable def logCoshRemainder (y : ℝ) : ℝ :=
  Real.log (1 + Real.exp (-2 * |y|))

/-- Exact factorization of `cosh` after extracting its dominant exponential. -/
theorem cosh_eq_exp_abs_factor (y : ℝ) :
    Real.cosh y = Real.exp |y| / 2 * (1 + Real.exp (-2 * |y|)) := by
  rw [← Real.cosh_abs y, Real.cosh_eq]
  have hexp : Real.exp (-|y|) = Real.exp |y| * Real.exp (-2 * |y|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Exact stable identity used for endpoint control:
`log(cosh y)=|y|-log 2+R(y)`. -/
theorem log_cosh_eq_abs_sub_log_two_add_remainder (y : ℝ) :
    Real.log (Real.cosh y) = |y| - Real.log 2 + logCoshRemainder y := by
  rw [cosh_eq_exp_abs_factor]
  have hexp : Real.exp |y| ≠ 0 := (Real.exp_pos _).ne'
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hfactor : 1 + Real.exp (-2 * |y|) ≠ 0 := by positivity
  rw [Real.log_mul (div_ne_zero hexp htwo) hfactor]
  rw [Real.log_div hexp htwo, Real.log_exp]
  unfold logCoshRemainder
  ring

/-- The correction is nonnegative. -/
theorem logCoshRemainder_nonneg (y : ℝ) : 0 ≤ logCoshRemainder y := by
  unfold logCoshRemainder
  apply Real.log_nonneg
  have hexp : 0 ≤ Real.exp (-2 * |y|) := (Real.exp_pos _).le
  linarith

/-- The correction is bounded by its exponentially small argument. -/
theorem logCoshRemainder_le_exp (y : ℝ) :
    logCoshRemainder y ≤ Real.exp (-2 * |y|) := by
  unfold logCoshRemainder
  have hpos : 0 < 1 + Real.exp (-2 * |y|) := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

/-- On the right endpoint region `x ≥ max(0,lam)`, the primitive differs from
`pi*lam` by exactly the difference of two exponentially small remainders. -/
theorem logCoshDifference_right_remainder
    {lam x : ℝ} (hx0 : 0 ≤ x) (hxlam : lam ≤ x) :
    logCoshDifference lam x - Real.pi * lam =
      logCoshRemainder (Real.pi * x) -
        logCoshRemainder (Real.pi * (lam - x)) := by
  unfold logCoshDifference
  rw [log_cosh_eq_abs_sub_log_two_add_remainder]
  rw [log_cosh_eq_abs_sub_log_two_add_remainder]
  have hpx : 0 ≤ Real.pi * x := mul_nonneg Real.pi_pos.le hx0
  have hshift : Real.pi * (lam - x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (sub_nonpos.mpr hxlam)
  rw [abs_of_nonneg hpx, abs_of_nonpos hshift]
  ring

/-- Quantitative right-endpoint error bound. -/
theorem abs_logCoshDifference_sub_right_limit_le
    {lam x : ℝ} (hx0 : 0 ≤ x) (hxlam : lam ≤ x) :
    |logCoshDifference lam x - Real.pi * lam| ≤
      Real.exp (-2 * |Real.pi * x|) +
        Real.exp (-2 * |Real.pi * (lam - x)|) := by
  rw [logCoshDifference_right_remainder hx0 hxlam]
  have h1 := logCoshRemainder_nonneg (Real.pi * x)
  have h2 := logCoshRemainder_nonneg (Real.pi * (lam - x))
  have hu1 := logCoshRemainder_le_exp (Real.pi * x)
  have hu2 := logCoshRemainder_le_exp (Real.pi * (lam - x))
  rw [abs_le]
  constructor <;> linarith

/-- On the left endpoint region `x ≤ min(0,lam)`, the primitive differs from
`-pi*lam` by exactly the same remainder difference. -/
theorem logCoshDifference_left_remainder
    {lam x : ℝ} (hx0 : x ≤ 0) (hxlam : x ≤ lam) :
    logCoshDifference lam x + Real.pi * lam =
      logCoshRemainder (Real.pi * x) -
        logCoshRemainder (Real.pi * (lam - x)) := by
  unfold logCoshDifference
  rw [log_cosh_eq_abs_sub_log_two_add_remainder]
  rw [log_cosh_eq_abs_sub_log_two_add_remainder]
  have hpx : Real.pi * x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hx0
  have hshift : 0 ≤ Real.pi * (lam - x) :=
    mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hxlam)
  rw [abs_of_nonpos hpx, abs_of_nonneg hshift]
  ring

/-- Quantitative left-endpoint error bound. -/
theorem abs_logCoshDifference_sub_left_limit_le
    {lam x : ℝ} (hx0 : x ≤ 0) (hxlam : x ≤ lam) :
    |logCoshDifference lam x + Real.pi * lam| ≤
      Real.exp (-2 * |Real.pi * x|) +
        Real.exp (-2 * |Real.pi * (lam - x)|) := by
  rw [logCoshDifference_left_remainder hx0 hxlam]
  have h1 := logCoshRemainder_nonneg (Real.pi * x)
  have h2 := logCoshRemainder_nonneg (Real.pi * (lam - x))
  have hu1 := logCoshRemainder_le_exp (Real.pi * x)
  have hu2 := logCoshRemainder_le_exp (Real.pi * (lam - x))
  rw [abs_le]
  constructor <;> linarith

/-- The first log-cosh term has derivative `pi * tanh(pi*x)`. -/
theorem hasDerivAt_log_cosh_pi_mul (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => Real.log (Real.cosh (Real.pi * y)))
      (Real.pi * (Real.sinh (Real.pi * x) / Real.cosh (Real.pi * x))) x := by
  have hlin : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
    convert (hasDerivAt_const x Real.pi).mul (hasDerivAt_id x) using 1 <;> ring
  have hc : Real.cosh (Real.pi * x) ≠ 0 := (Real.cosh_pos _).ne'
  have h := ((Real.hasDerivAt_cosh (Real.pi * x)).comp x hlin).log hc
  convert h using 1
  field_simp [hc]
  ring

/-- The reflected log-cosh term has derivative `-pi * tanh(pi*(lambda-x))`. -/
theorem hasDerivAt_log_cosh_pi_shift (lam x : ℝ) :
    HasDerivAt
      (fun y : ℝ => Real.log (Real.cosh (Real.pi * (lam - y))))
      (-Real.pi *
        (Real.sinh (Real.pi * (lam - x)) / Real.cosh (Real.pi * (lam - x)))) x := by
  have hsub : HasDerivAt (fun y : ℝ => lam - y) (-1) x := by
    convert (hasDerivAt_const x lam).sub (hasDerivAt_id x) using 1 <;> ring
  have hlin : HasDerivAt (fun y : ℝ => Real.pi * (lam - y)) (-Real.pi) x := by
    convert (hasDerivAt_const x Real.pi).mul hsub using 1 <;> ring
  have hc : Real.cosh (Real.pi * (lam - x)) ≠ 0 := (Real.cosh_pos _).ne'
  have hcosh0 := (Real.hasDerivAt_cosh (Real.pi * (lam - x))).comp x hlin
  have hcosh : HasDerivAt
      (fun y : ℝ => Real.cosh (Real.pi * (lam - y)))
      (Real.sinh (Real.pi * (lam - x)) * (-Real.pi)) x := by
    simpa only [Function.comp_apply] using hcosh0
  have h := hcosh.log hc
  convert h using 1
  field_simp [hc]
  ring

/-- Exact primitive derivative for the shifted sech-product kernel:

`d/dx [log cosh(pi*x) - log cosh(pi*(lambda-x))]
 = pi*sinh(pi*lambda)/(cosh(pi*x) cosh(pi*(lambda-x)))`.

This is the finite-endpoint interface needed before taking the whole-line limit. -/
theorem hasDerivAt_logCoshDifference (lam x : ℝ) :
    HasDerivAt (logCoshDifference lam)
      (Real.pi * Real.sinh (Real.pi * lam) /
        (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x)))) x := by
  have h1 := hasDerivAt_log_cosh_pi_mul x
  have h2 := hasDerivAt_log_cosh_pi_shift lam x
  have h := h1.sub h2
  have hx : Real.cosh (Real.pi * x) ≠ 0 := (Real.cosh_pos _).ne'
  have hshift : Real.cosh (Real.pi * (lam - x)) ≠ 0 := (Real.cosh_pos _).ne'
  have hk := pi_shift_kernel_identity x lam hx hshift
  have hcoef :
      Real.pi * (Real.sinh (Real.pi * x) / Real.cosh (Real.pi * x)) -
          (-Real.pi *
            (Real.sinh (Real.pi * (lam - x)) / Real.cosh (Real.pi * (lam - x)))) =
        Real.pi * Real.sinh (Real.pi * lam) /
          (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x))) := by
    rw [show
      Real.pi * (Real.sinh (Real.pi * x) / Real.cosh (Real.pi * x)) -
          (-Real.pi *
            (Real.sinh (Real.pi * (lam - x)) / Real.cosh (Real.pi * (lam - x)))) =
        Real.pi *
          (Real.sinh (Real.pi * x) / Real.cosh (Real.pi * x) +
            Real.sinh (Real.pi * (lam - x)) / Real.cosh (Real.pi * (lam - x))) by ring]
    rw [hk]
    ring
  rw [hcoef] at h
  simpa [logCoshDifference] using h

end GppSechConvolutionPrimitive

#print axioms GppSechConvolutionPrimitive.cosh_eq_exp_abs_factor
#print axioms GppSechConvolutionPrimitive.log_cosh_eq_abs_sub_log_two_add_remainder
#print axioms GppSechConvolutionPrimitive.abs_logCoshDifference_sub_right_limit_le
#print axioms GppSechConvolutionPrimitive.abs_logCoshDifference_sub_left_limit_le
#print axioms GppSechConvolutionPrimitive.hasDerivAt_log_cosh_pi_mul
#print axioms GppSechConvolutionPrimitive.hasDerivAt_log_cosh_pi_shift
#print axioms GppSechConvolutionPrimitive.hasDerivAt_logCoshDifference
