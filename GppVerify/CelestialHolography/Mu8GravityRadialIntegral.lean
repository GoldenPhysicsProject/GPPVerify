import GppVerify.CelestialHolography.Mu2BubbleRadialIntegral

/-!
# The `mu^8` four-graviton all-plus radial shell

Bern-Dixon-Perelstein-Rozowsky's D-dimensional four-graviton all-plus cut is a sum
of scalar boxes with numerator `mu^8`. With `mu = M/(2 cosh r)`, two-body phase
space therefore supplies the universal radial shell

  `tanh r / cosh^8 r`.

This file proves its exact half-line normalization `1/8`.
-/

namespace GppMu8GravityRadial

open Filter MeasureTheory
open GppSechIntegral GppMu2BubbleRadial

/-- A convenient antiderivative of the `mu^8` gravity shell. -/
noncomputable def gravityShellAntideriv (r : ℝ) : ℝ :=
  -(1 / 8 : ℝ) * (1 - Real.tanh r ^ 2) ^ 4

/-- The derivative is exactly `tanh r / cosh^8 r`. -/
theorem hasDerivAt_gravityShellAntideriv (r : ℝ) :
    HasDerivAt gravityShellAntideriv
      (Real.tanh r / Real.cosh r ^ 8) r := by
  have ht := hasDerivAt_tanh' r
  have hsq := (ht.pow 2)
  have hinner := (hasDerivAt_const r (1 : ℝ)).sub hsq
  have hpow := (hinner.pow 4).const_mul (-(1 / 8 : ℝ))
  convert hpow using 1
  · unfold gravityShellAntideriv
  · rw [show Real.cosh r ^ 8 = (Real.cosh r ^ 2) ^ 4 by ring]
    rw [show 1 / (Real.cosh r ^ 2) ^ 4 = (1 / Real.cosh r ^ 2) ^ 4 by field_simp]
    rw [one_div_cosh_sq]
    ring

/-- Threshold value of the antiderivative. -/
theorem gravityShellAntideriv_zero :
    gravityShellAntideriv 0 = -(1 / 8 : ℝ) := by
  simp [gravityShellAntideriv]

/-- The antiderivative vanishes at the massless boundary. -/
theorem tendsto_gravityShellAntideriv_zero :
    Tendsto gravityShellAntideriv atTop (nhds 0) := by
  have hsq := tendsto_tanh_sq_one
  have hsub := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub hsq
  have hpow := hsub.pow 4
  have h := hpow.const_mul (-(1 / 8 : ℝ))
  simpa [gravityShellAntideriv] using h

/-- The gravity shell is nonnegative above threshold. -/
theorem gravityShell_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ Real.tanh r / Real.cosh r ^ 8 := by
  have hsinh : 0 ≤ Real.sinh r := by
    rw [Real.sinh_eq]
    have h := Real.exp_le_exp.mpr (by linarith : -r ≤ r)
    linarith
  have htanh : 0 ≤ Real.tanh r := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg hsinh (Real.cosh_pos r).le
  exact div_nonneg htanh (by positivity)

/-- **Exact `mu^8` all-plus gravity shell normalization**:
`∫_0^∞ tanh r sech^8 r dr = 1/8`. -/
theorem integral_gravityShell :
    ∫ r in Set.Ioi (0 : ℝ), Real.tanh r / Real.cosh r ^ 8 = 1 / 8 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    ((hasDerivAt_gravityShellAntideriv 0).continuousAt.continuousWithinAt)
    (fun r _ => hasDerivAt_gravityShellAntideriv r)
    (fun r hr => gravityShell_nonneg hr)
    tendsto_gravityShellAntideriv_zero
  rw [gravityShellAntideriv_zero] at h
  linarith

end GppMu8GravityRadial

#print axioms GppMu8GravityRadial.integral_gravityShell
