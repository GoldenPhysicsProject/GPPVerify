import GppVerify.CelestialHolography.ContinuousSechLevyFrequencyDerivativeBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Exponential tail infrastructure for the continuous sech Lévy derivative

The global derivative bound controls the origin but is not integrable at infinity.
This file isolates the exact hyperbolic-sine lower bound and the resulting exponential
decay on `|x| >= 1`.  It is deliberately kept separate from differentiation under the
integral.
-/

namespace GppContinuousSechLevyFrequencyDerivativeTail

open GppContinuousSechLevyKernel
open GppContinuousSechLevyFrequencyDerivative

/-- On `|x| >= 1`, the hyperbolic denominator admits an explicit exponential lower
bound with no numerical approximation of `pi` or `exp (-2*pi)`. -/
theorem sinh_tail_lower {x : ℝ} (hx : 1 ≤ |x|) :
    ((1 - Real.exp (-(2 * Real.pi))) / 2) * Real.exp (Real.pi * |x|) ≤
      Real.sinh (Real.pi * |x|) := by
  let y : ℝ := Real.pi * |x|
  have hy : Real.pi ≤ y := by
    dsimp [y]
    nlinarith [Real.pi_pos]
  have hmono : Real.exp (-(2 * y)) ≤ Real.exp (-(2 * Real.pi)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have htail :
      Real.exp (-y) ≤ Real.exp y * Real.exp (-(2 * Real.pi)) := by
    calc
      Real.exp (-y) = Real.exp y * Real.exp (-(2 * y)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp y * Real.exp (-(2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hmono (Real.exp_pos y).le
  have hcore :
      ((1 - Real.exp (-(2 * Real.pi))) / 2) * Real.exp y ≤ Real.sinh y := by
    rw [Real.sinh_eq]
    nlinarith
  simpa [y] using hcore

/-- On the spatial tail `|x| >= 1`, the frequency-derivative kernel has an
explicit exponential majorant independent of the frequency `t`. -/
theorem abs_frequencyDerivativeKernel_le_exp_tail {c t x : ℝ}
    (hc : 0 ≤ c) (hx : 1 ≤ |x|) :
    |frequencyDerivativeKernel c t x| ≤
      (2 * c / (1 - Real.exp (-(2 * Real.pi)))) * Real.exp (-(Real.pi * |x|)) := by
  have hxabs : 0 < |x| := lt_of_lt_of_le zero_lt_one hx
  have hsinh : 0 < Real.sinh (Real.pi * |x|) := by
    exact Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hxabs)
  have hexp_lt_one : Real.exp (-(2 * Real.pi)) < 1 := by
    exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hgap : 0 < 1 - Real.exp (-(2 * Real.pi)) := sub_pos.mpr hexp_lt_one
  have hsin : |Real.sin (t * x)| ≤ 1 := abs_sin_le_one (t * x)
  have hkernel :
      |frequencyDerivativeKernel c t x| =
        c * |Real.sin (t * x)| / Real.sinh (Real.pi * |x|) := by
    unfold frequencyDerivativeKernel levyDensity
    rw [abs_mul, abs_mul, abs_div, abs_mul, abs_abs]
    rw [abs_of_nonneg hc, abs_of_pos hsinh]
    field_simp [ne_of_gt hxabs, ne_of_gt hsinh]
  have hfirst :
      c * |Real.sin (t * x)| / Real.sinh (Real.pi * |x|) ≤
        c / Real.sinh (Real.pi * |x|) := by
    apply (div_le_div_iff_of_pos_right hsinh).2
    exact mul_le_of_le_one_right hc hsin
  have htail := sinh_tail_lower (x := x) hx
  let A : ℝ := (1 - Real.exp (-(2 * Real.pi))) / 2
  let B : ℝ := (2 * c / (1 - Real.exp (-(2 * Real.pi)))) *
    Real.exp (-(Real.pi * |x|))
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hscaled :
      B * (A * Real.exp (Real.pi * |x|)) ≤
        B * Real.sinh (Real.pi * |x|) := by
    exact mul_le_mul_of_nonneg_left (by simpa [A] using htail) hB
  have hcancel : B * (A * Real.exp (Real.pi * |x|)) = c := by
    dsimp [A, B]
    rw [← Real.exp_add]
    have hsum : -(Real.pi * |x|) + Real.pi * |x| = 0 := by ring
    rw [hsum, Real.exp_zero]
    field_simp [ne_of_gt hgap]
    ring
  have hsecond : c / Real.sinh (Real.pi * |x|) ≤ B := by
    apply (div_le_iff₀ hsinh).2
    calc
      c = B * (A * Real.exp (Real.pi * |x|)) := hcancel.symm
      _ ≤ B * Real.sinh (Real.pi * |x|) := hscaled
  rw [hkernel]
  calc
    c * |Real.sin (t * x)| / Real.sinh (Real.pi * |x|)
        ≤ c / Real.sinh (Real.pi * |x|) := hfirst
    _ ≤ B := hsecond
    _ = (2 * c / (1 - Real.exp (-(2 * Real.pi)))) *
      Real.exp (-(Real.pi * |x|)) := by rfl

end GppContinuousSechLevyFrequencyDerivativeTail

#print axioms GppContinuousSechLevyFrequencyDerivativeTail.sinh_tail_lower
#print axioms GppContinuousSechLevyFrequencyDerivativeTail.abs_frequencyDerivativeKernel_le_exp_tail
