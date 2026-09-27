import GppVerify.CelestialHolography.ContinuousSechLevyFrequencyDerivativeTail
import GppVerify.CelestialHolography.ContinuousSechLevyIntegrable

/-!
# Parameter-uniform integrable majorant for the continuous sech Lévy derivative

The compensated Lévy kernel has formal frequency derivative

  D_c(t,x) = x sin(t x) nu_c(x).

The previously certified bounds control the core by `c * |t| / pi` and the tail by an
explicit exponential.  This file converts the exponential tail to inverse-square decay
and packages both pieces into one Cauchy majorant, uniform for every frequency satisfying
`|t| <= T`.  This is the analytic domination input needed before differentiating the
Lévy integral with respect to `t`.
-/

namespace GppContinuousSechLevyFrequencyDerivativeMajorant

open MeasureTheory
open GppContinuousSechLevyFrequencyDerivative
open GppContinuousSechLevyFrequencyDerivativeBound
open GppContinuousSechLevyFrequencyDerivativeTail

/-- On `|x| >= 1`, the exponential tail is itself bounded by `|x|⁻²`.
The proof uses only `2 <= pi` and the elementary lower bound `1+y <= exp y`. -/
theorem exp_neg_pi_abs_le_inv_sq {x : ℝ} (hx : 1 ≤ |x|) :
    Real.exp (-(Real.pi * |x|)) ≤ (|x| ^ 2)⁻¹ := by
  have hxpos : 0 < |x| := lt_of_lt_of_le zero_lt_one hx
  have hpi_mul : 2 * |x| ≤ Real.pi * |x| :=
    mul_le_mul_of_nonneg_right Real.two_le_pi (abs_nonneg x)
  have hy : |x| ≤ Real.pi * |x| / 2 := by
    nlinarith
  have hlin :
      1 + Real.pi * |x| / 2 ≤ Real.exp (Real.pi * |x| / 2) :=
    Real.add_one_le_exp _
  have hbase : |x| ≤ Real.exp (Real.pi * |x| / 2) := by
    calc
      |x| ≤ Real.pi * |x| / 2 := hy
      _ ≤ 1 + Real.pi * |x| / 2 := by linarith
      _ ≤ Real.exp (Real.pi * |x| / 2) := hlin
  have hsq :
      |x| ^ 2 ≤ (Real.exp (Real.pi * |x| / 2)) ^ 2 := by
    nlinarith [abs_nonneg x, (Real.exp_pos (Real.pi * |x| / 2)).le]
  have hexp_sq :
      (Real.exp (Real.pi * |x| / 2)) ^ 2 = Real.exp (Real.pi * |x|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq_exp : |x| ^ 2 ≤ Real.exp (Real.pi * |x|) := by
    calc
      |x| ^ 2 ≤ (Real.exp (Real.pi * |x| / 2)) ^ 2 := hsq
      _ = Real.exp (Real.pi * |x|) := hexp_sq
  have hprod :
      Real.exp (-(Real.pi * |x|)) * |x| ^ 2 ≤ 1 := by
    calc
      Real.exp (-(Real.pi * |x|)) * |x| ^ 2
          ≤ Real.exp (-(Real.pi * |x|)) * Real.exp (Real.pi * |x|) :=
        mul_le_mul_of_nonneg_left hsq_exp (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        have hzero : -(Real.pi * |x|) + Real.pi * |x| = 0 := by ring
        rw [hzero, Real.exp_zero]
  rw [inv_eq_one_div]
  exact (le_div_iff₀ (sq_pos_of_pos hxpos)).2 hprod

/-- The derivative kernel therefore has an inverse-square tail, with the same exact
frequency-independent coefficient inherited from the sharp exponential estimate. -/
theorem abs_frequencyDerivativeKernel_le_inv_sq {c t x : ℝ}
    (hc : 0 ≤ c) (hx : 1 ≤ |x|) :
    |frequencyDerivativeKernel c t x| ≤
      (2 * c / (1 - Real.exp (-(2 * Real.pi)))) / (|x| ^ 2) := by
  have hgap : 0 < 1 - Real.exp (-(2 * Real.pi)) := by
    have : Real.exp (-(2 * Real.pi)) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    linarith
  have hA : 0 ≤ 2 * c / (1 - Real.exp (-(2 * Real.pi))) := by positivity
  have htail := abs_frequencyDerivativeKernel_le_exp_tail (c := c) (t := t) (x := x) hc hx
  have hexp := exp_neg_pi_abs_le_inv_sq (x := x) hx
  calc
    |frequencyDerivativeKernel c t x|
        ≤ (2 * c / (1 - Real.exp (-(2 * Real.pi)))) *
            Real.exp (-(Real.pi * |x|)) := htail
    _ ≤ (2 * c / (1 - Real.exp (-(2 * Real.pi)))) * (|x| ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hexp hA
    _ = (2 * c / (1 - Real.exp (-(2 * Real.pi)))) / (|x| ^ 2) := by
      rw [div_eq_mul_inv]

/-- One explicit global Cauchy-majorant coefficient, uniform on the frequency window
`|t| <= T`. -/
def frequencyDerivativeCauchyConstant (c T : ℝ) : ℝ :=
  2 * (c * T / Real.pi + 2 * c / (1 - Real.exp (-(2 * Real.pi))))

/-- Uniform Cauchy domination of the derivative kernel on a compact frequency window. -/
theorem abs_frequencyDerivativeKernel_le_cauchy {c T t x : ℝ}
    (hc : 0 ≤ c) (ht : |t| ≤ T) :
    |frequencyDerivativeKernel c t x| ≤
      frequencyDerivativeCauchyConstant c T * (1 + x ^ 2)⁻¹ := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hgap : 0 < 1 - Real.exp (-(2 * Real.pi)) := by
    have : Real.exp (-(2 * Real.pi)) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    linarith
  have hC : 0 ≤ frequencyDerivativeCauchyConstant c T := by
    unfold frequencyDerivativeCauchyConstant
    positivity
  have hden : 0 < 1 + x ^ 2 := by positivity
  by_cases hx : |x| ≤ 1
  · have hcore := abs_frequencyDerivativeKernel_le (c := c) (t := t) (x := x) hc
    have htcore : c * |t| / Real.pi ≤ c * T / Real.pi := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht hc) Real.pi_pos.le
    have hden_le : 1 + x ^ 2 ≤ 2 := by
      have hx' := abs_le.mp hx
      nlinarith [sq_nonneg x]
    have hhalf :
        c * T / Real.pi ≤ frequencyDerivativeCauchyConstant c T / 2 := by
      unfold frequencyDerivativeCauchyConstant
      have htailnonneg : 0 ≤ 2 * c / (1 - Real.exp (-(2 * Real.pi))) := by positivity
      linarith
    have hdiv :
        frequencyDerivativeCauchyConstant c T / 2 ≤
          frequencyDerivativeCauchyConstant c T / (1 + x ^ 2) := by
      exact div_le_div_of_nonneg_left hC hden hden_le
    calc
      |frequencyDerivativeKernel c t x| ≤ c * |t| / Real.pi := hcore
      _ ≤ c * T / Real.pi := htcore
      _ ≤ frequencyDerivativeCauchyConstant c T / 2 := hhalf
      _ ≤ frequencyDerivativeCauchyConstant c T / (1 + x ^ 2) := hdiv
      _ = frequencyDerivativeCauchyConstant c T * (1 + x ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]
  · have hxgt : 1 < |x| := lt_of_not_ge hx
    have hx1 : 1 ≤ |x| := hxgt.le
    have htail := abs_frequencyDerivativeKernel_le_inv_sq (c := c) (t := t) (x := x) hc hx1
    have hx2 : 1 ≤ |x| ^ 2 := by nlinarith [sq_nonneg |x|]
    have hx2pos : 0 < |x| ^ 2 := by positivity
    have hden_le : 1 + x ^ 2 ≤ 2 * |x| ^ 2 := by
      rw [sq_abs]
      nlinarith
    have htailconst :
        2 * c / (1 - Real.exp (-(2 * Real.pi))) ≤
          frequencyDerivativeCauchyConstant c T / 2 := by
      unfold frequencyDerivativeCauchyConstant
      have hcore_nonneg : 0 ≤ c * T / Real.pi := by positivity
      linarith
    have hstep1 :
        (2 * c / (1 - Real.exp (-(2 * Real.pi)))) / (|x| ^ 2) ≤
          (frequencyDerivativeCauchyConstant c T / 2) / (|x| ^ 2) :=
      div_le_div_of_nonneg_right htailconst hx2pos.le
    have hstep2 :
        (frequencyDerivativeCauchyConstant c T / 2) / (|x| ^ 2) ≤
          frequencyDerivativeCauchyConstant c T / (1 + x ^ 2) := by
      have hleft :
          (frequencyDerivativeCauchyConstant c T / 2) / (|x| ^ 2) =
            frequencyDerivativeCauchyConstant c T / (2 * |x| ^ 2) := by ring
      rw [hleft]
      exact div_le_div_of_nonneg_left hC hden hden_le
    calc
      |frequencyDerivativeKernel c t x|
          ≤ (2 * c / (1 - Real.exp (-(2 * Real.pi)))) / (|x| ^ 2) := htail
      _ ≤ (frequencyDerivativeCauchyConstant c T / 2) / (|x| ^ 2) := hstep1
      _ ≤ frequencyDerivativeCauchyConstant c T / (1 + x ^ 2) := hstep2
      _ = frequencyDerivativeCauchyConstant c T * (1 + x ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]

/-- The parameter-uniform Cauchy majorant is genuinely Lebesgue integrable on `ℝ`. -/
theorem integrable_frequencyDerivativeCauchyMajorant (c T : ℝ) :
    Integrable (fun x : ℝ =>
      frequencyDerivativeCauchyConstant c T * (1 + x ^ 2)⁻¹) :=
  Integrable.const_mul integrable_inv_one_add_sq (frequencyDerivativeCauchyConstant c T)

end GppContinuousSechLevyFrequencyDerivativeMajorant

#print axioms GppContinuousSechLevyFrequencyDerivativeMajorant.exp_neg_pi_abs_le_inv_sq
#print axioms GppContinuousSechLevyFrequencyDerivativeMajorant.abs_frequencyDerivativeKernel_le_inv_sq
#print axioms GppContinuousSechLevyFrequencyDerivativeMajorant.abs_frequencyDerivativeKernel_le_cauchy
#print axioms GppContinuousSechLevyFrequencyDerivativeMajorant.integrable_frequencyDerivativeCauchyMajorant
