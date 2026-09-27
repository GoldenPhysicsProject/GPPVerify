import GppVerify.CelestialHolography.Mu2BubbleRadialIntegral

/-!
# Universal `mu^(2r)` celestial radial-shell integral

For every positive integer `r`, the fixed-radius two-particle phase-space shell
associated with a `mu^(2r)` numerator is

  `tanh x / cosh(x)^(2r)`.

This file proves the whole family at once:

  `integral_0^infty tanh x sech^(2r) x dx = 1/(2r)`.

We parametrize `r = k+1` to make positivity automatic and avoid predecessor cases.
-/

namespace GppMu2kRadial

open Filter MeasureTheory
open GppSechIntegral GppMu2BubbleRadial

/-- Universal antiderivative for the shell with numerator power `r=k+1`. -/
noncomputable def radialAntideriv (k : ℕ) (x : ℝ) : ℝ :=
  -(1 / (2 * ((k : ℝ) + 1))) * (1 - Real.tanh x ^ 2) ^ (k + 1)

/-- Derivative of the universal antiderivative. -/
theorem hasDerivAt_radialAntideriv (k : ℕ) (x : ℝ) :
    HasDerivAt (radialAntideriv k)
      (Real.tanh x / Real.cosh x ^ (2 * (k + 1))) x := by
  have ht := hasDerivAt_tanh' x
  have hsq := ht.pow 2
  have hinner := (hasDerivAt_const x (1 : ℝ)).sub hsq
  have hpow := (hinner.pow (k + 1)).const_mul
    (-(1 / (2 * ((k : ℝ) + 1))))
  have hcosh :
      1 / Real.cosh x ^ (2 * (k + 1)) =
        (1 - Real.tanh x ^ 2) ^ (k + 1) := by
    rw [show Real.cosh x ^ (2 * (k + 1)) =
      (Real.cosh x ^ 2) ^ (k + 1) by rw [pow_mul]]
    rw [one_div_pow, one_div_cosh_sq]
  convert hpow using 1
  · rfl
  · rw [hcosh, div_eq_mul_inv]
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [pow_succ]
    push_cast
    field_simp [hk]
    ring

/-- Threshold value. -/
theorem radialAntideriv_zero (k : ℕ) :
    radialAntideriv k 0 = -(1 / (2 * ((k : ℝ) + 1))) := by
  simp [radialAntideriv]

/-- Every positive-power radial antiderivative vanishes at the massless boundary. -/
theorem tendsto_radialAntideriv_zero (k : ℕ) :
    Tendsto (radialAntideriv k) atTop (nhds 0) := by
  have hsq := tendsto_tanh_sq_one
  have hsub := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub hsq
  have hpow := hsub.pow (k + 1)
  have h := hpow.const_mul (-(1 / (2 * ((k : ℝ) + 1))))
  simpa [radialAntideriv] using h

/-- The universal shell is nonnegative above threshold. -/
theorem radialShell_nonneg (k : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ Real.tanh x / Real.cosh x ^ (2 * (k + 1)) := by
  have hsinh : 0 ≤ Real.sinh x := by
    rw [Real.sinh_eq]
    have h := Real.exp_le_exp.mpr (by linarith : -x ≤ x)
    linarith
  have htanh : 0 ≤ Real.tanh x := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg hsinh (Real.cosh_pos x).le
  exact div_nonneg htanh (by positivity)

/-- **Universal radial normalization** for every positive integer numerator power. -/
theorem integral_radialShell (k : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ),
      Real.tanh x / Real.cosh x ^ (2 * (k + 1)) =
      1 / (2 * ((k : ℝ) + 1)) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    ((hasDerivAt_radialAntideriv k 0).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_radialAntideriv k x)
    (fun x hx => radialShell_nonneg k hx)
    (tendsto_radialAntideriv_zero k)
  rw [radialAntideriv_zero] at h
  linarith

/-- **Exact radial tail law.** Above any nonnegative radius `R`, the remaining shell mass
is the threshold normalization times `sech(R)^(2r)`. -/
theorem integral_radialShell_tail (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in Set.Ioi R,
      Real.tanh x / Real.cosh x ^ (2 * (k + 1)) =
      (1 / (2 * ((k : ℝ) + 1))) *
        (1 / Real.cosh R ^ (2 * (k + 1))) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    ((hasDerivAt_radialAntideriv k R).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_radialAntideriv k x)
    (fun x hx => radialShell_nonneg k (lt_of_le_of_lt hR hx))
    (tendsto_radialAntideriv_zero k)
  have hcosh :
      1 / Real.cosh R ^ (2 * (k + 1)) =
        (1 - Real.tanh R ^ 2) ^ (k + 1) := by
    rw [show Real.cosh R ^ (2 * (k + 1)) =
      (Real.cosh R ^ 2) ^ (k + 1) by rw [pow_mul]]
    rw [one_div_pow, one_div_cosh_sq]
  rw [hcosh]
  simpa [radialAntideriv] using h

/-- After multiplying by the normalization `2r`, the survival function is exactly
`sech(R)^(2r)`. This is the formal content of the uniformizing variable
`U = sech(R)^(2r) = (2 mu/M)^(2r)`. -/
theorem normalized_radialTail (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (2 * ((k : ℝ) + 1)) *
      (∫ x in Set.Ioi R,
        Real.tanh x / Real.cosh x ^ (2 * (k + 1))) =
      1 / Real.cosh R ^ (2 * (k + 1)) := by
  rw [integral_radialShell_tail k hR]
  have hk : (2 * ((k : ℝ) + 1)) ≠ 0 := by positivity
  field_simp [hk]

/-- The `mu^2` bubble shell is the `k=0` member. -/
theorem integral_mu2_shell :
    ∫ x in Set.Ioi (0 : ℝ), Real.tanh x / Real.cosh x ^ 2 = 1 / 2 := by
  simpa using integral_radialShell 0

/-- The `mu^8` all-plus-gravity box shell is the `k=3` member. -/
theorem integral_mu8_shell :
    ∫ x in Set.Ioi (0 : ℝ), Real.tanh x / Real.cosh x ^ 8 = 1 / 8 := by
  simpa using integral_radialShell 3

end GppMu2kRadial

#print axioms GppMu2kRadial.integral_radialShell
#print axioms GppMu2kRadial.integral_radialShell_tail
#print axioms GppMu2kRadial.normalized_radialTail
