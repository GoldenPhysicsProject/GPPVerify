import GppVerify.CelestialHolography.ScalarBoxProductEndpointBounds
import GppVerify.CelestialHolography.ScalarBoxPoleEndpointScale
import GppVerify.CelestialHolography.ScalarBoxLogBounds
import GppVerify.CelestialHolography.RegulatedBoxDilogSeries
import Mathlib.Tactic

/-!
# Scalar-box special-function remainder

This file promotes the small special-function remainder from the structured
regulated-box analysis.  It deliberately keeps the moving-endpoint logarithm
bound as a separate input: the remaining task after this file is to derive that
bound from the exact factorization `q = rho * Q` and the certified interval for
`Q`.
-/

namespace GppScalarBoxSpecialFunctionRemainder

open GppRegulatedBoxDilogSeries

/-- The exact small special-function remainder after the Spence and reciprocal
identities have removed all large dilogarithm arguments. -/
noncomputable def specialRemainder (a q t : ℝ) : ℝ :=
  -li2Series (-t) - li2Series (a * q) -
    Real.log q * Real.log (1 - a * q) -
    (1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2 -
    li2Series (-(a / (1 - a))) + li2Series a

/-- Dimensionless structured majorant used in the final regulator theorem. -/
noncomputable def specialRemainderMajorant (ρ η : ℝ) : ℝ :=
  (48 / 19 : ℝ) * η + (232 / 105 : ℝ) * ρ +
    ((648 / 289 : ℝ) + (9 / 8 : ℝ)) * ρ ^ 2 +
    (486 / 289 : ℝ) * ρ ^ 2 *
      (|Real.log ρ| + (81 / 32 : ℝ) * ρ)

/-- The positive lower-endpoint dilogarithm is bounded linearly by `rho`. -/
theorem abs_li2Series_a_le_rho
    {a ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 16)
    (ha0 : 0 ≤ a) (haρ : a ≤ ρ) :
    |li2Series a| ≤ (16 / 15 : ℝ) * ρ := by
  have ha1 : a < 1 := lt_of_le_of_lt (haρ.trans hρ) (by norm_num)
  have hli := abs_li2Series_le_of_nonneg ha0 ha1
  have hden : 0 < 1 - a := by linarith
  calc
    |li2Series a| ≤ a / (1 - a) := hli
    _ ≤ (16 / 15 : ℝ) * ρ := by
      apply (div_le_iff₀ hden).2
      have hfac : (15 / 16 : ℝ) ≤ 1 - a := by linarith
      have hm := mul_le_mul_of_nonneg_left hfac hρ0
      nlinarith

/-- The negative transformed lower endpoint `-a/(1-a)` is also uniformly linear
in `rho`. -/
theorem abs_li2Series_neg_a_div_one_sub_a_le_rho
    {a ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 16)
    (ha0 : 0 ≤ a) (haρ : a ≤ ρ) :
    |li2Series (-(a / (1 - a)))| ≤ (8 / 7 : ℝ) * ρ := by
  have hden : 0 < 1 - a := by linarith
  have hx0 : 0 ≤ a / (1 - a) := div_nonneg ha0 hden.le
  have h2a : 0 < 1 - 2 * a := by linarith
  have hx1 : a / (1 - a) < 1 := by
    apply (div_lt_iff₀ hden).2
    linarith
  have hli := abs_li2Series_neg_le_of_nonneg hx0 hx1
  have hinner :
      (1 - a) * (1 - a / (1 - a)) = 1 - 2 * a := by
    field_simp [hden.ne']
    ring
  have hrewrite :
      (a / (1 - a)) / (1 - a / (1 - a)) = a / (1 - 2 * a) := by
    rw [div_div, hinner]
  rw [hrewrite] at hli
  calc
    |li2Series (-(a / (1 - a)))| ≤ a / (1 - 2 * a) := hli
    _ ≤ (8 / 7 : ℝ) * ρ := by
      apply (div_le_iff₀ h2a).2
      have hfac : (7 / 8 : ℝ) ≤ 1 - 2 * a := by linarith
      have hm := mul_le_mul_of_nonneg_left hfac hρ0
      nlinarith

/-- The two lower-endpoint dilogarithm corrections combine to the exact coefficient
`232/105`. -/
theorem lower_endpoint_li2_pair_le
    {a ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 16)
    (ha0 : 0 ≤ a) (haρ : a ≤ ρ) :
    |li2Series (-(a / (1 - a)))| + |li2Series a| ≤
      (232 / 105 : ℝ) * ρ := by
  have hneg := abs_li2Series_neg_a_div_one_sub_a_le_rho hρ0 hρ ha0 haρ
  have hpos := abs_li2Series_a_le_rho hρ0 hρ ha0 haρ
  nlinarith

/-- Abstract assembly of the exact structured `E_*` bound.  All six component
estimates are independent certified interfaces; the only not-yet-physical input is
`hqlog`, the moving-endpoint logarithmic scale estimate. -/
theorem abs_specialRemainder_le
    {a q t ρ η : ℝ}
    (hρ0 : 0 ≤ ρ) (hη0 : 0 ≤ η)
    (ht : |li2Series (-t)| ≤ (48 / 19 : ℝ) * η)
    (haqLi : |li2Series (a * q)| ≤ (648 / 289 : ℝ) * ρ ^ 2)
    (hqlog : |Real.log q| ≤ |Real.log ρ| + (81 / 32 : ℝ) * ρ)
    (haqLog : |Real.log (1 - a * q)| ≤ (486 / 289 : ℝ) * ρ ^ 2)
    (haLog : (1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2 ≤ (9 / 8 : ℝ) * ρ ^ 2)
    (haNeg : |li2Series (-(a / (1 - a)))| ≤ (8 / 7 : ℝ) * ρ)
    (haPos : |li2Series a| ≤ (16 / 15 : ℝ) * ρ) :
    |specialRemainder a q t| ≤ specialRemainderMajorant ρ η := by
  have hq0 : 0 ≤ |Real.log q| := abs_nonneg _
  have hlogprod :
      |Real.log q * Real.log (1 - a * q)| ≤
        (486 / 289 : ℝ) * ρ ^ 2 *
          (|Real.log ρ| + (81 / 32 : ℝ) * ρ) := by
    rw [abs_mul]
    calc
      |Real.log q| * |Real.log (1 - a * q)| ≤
          (|Real.log ρ| + (81 / 32 : ℝ) * ρ) *
            ((486 / 289 : ℝ) * ρ ^ 2) :=
        mul_le_mul hqlog haqLog (abs_nonneg _) (by positivity)
      _ = (486 / 289 : ℝ) * ρ ^ 2 *
          (|Real.log ρ| + (81 / 32 : ℝ) * ρ) := by ring
  have haLogAbs :
      |(1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2| ≤ (9 / 8 : ℝ) * ρ ^ 2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2)]
    exact haLog
  unfold specialRemainder specialRemainderMajorant
  calc
    |-li2Series (-t) - li2Series (a * q) -
        Real.log q * Real.log (1 - a * q) -
        (1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2 -
        li2Series (-(a / (1 - a))) + li2Series a| ≤
      |li2Series (-t)| + |li2Series (a * q)| +
        |Real.log q * Real.log (1 - a * q)| +
        |(1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2| +
        |li2Series (-(a / (1 - a)))| + |li2Series a| := by
          calc
            _ ≤ |-li2Series (-t) - li2Series (a * q) -
                    Real.log q * Real.log (1 - a * q) -
                    (1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2 -
                    li2Series (-(a / (1 - a)))| + |li2Series a| := abs_add _ _
            _ ≤ (|-li2Series (-t) - li2Series (a * q) -
                    Real.log q * Real.log (1 - a * q) -
                    (1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2| +
                    |li2Series (-(a / (1 - a)))|) + |li2Series a| := by
                  gcongr
                  exact abs_sub _ _
            _ ≤ ((|-li2Series (-t) - li2Series (a * q) -
                    Real.log q * Real.log (1 - a * q)| +
                    |(1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2|) +
                    |li2Series (-(a / (1 - a)))|) + |li2Series a| := by
                  gcongr
                  exact abs_sub _ _
            _ ≤ (((|-li2Series (-t) - li2Series (a * q)| +
                    |Real.log q * Real.log (1 - a * q)|) +
                    |(1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2|) +
                    |li2Series (-(a / (1 - a)))|) + |li2Series a| := by
                  gcongr
                  exact abs_sub _ _
            _ ≤ ((((|li2Series (-t)| + |li2Series (a * q)|) +
                    |Real.log q * Real.log (1 - a * q)|) +
                    |(1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2|) +
                    |li2Series (-(a / (1 - a)))|) + |li2Series a| := by
                  simpa using (abs_sub (-li2Series (-t)) (li2Series (a * q)))
            _ = |li2Series (-t)| + |li2Series (a * q)| +
                |Real.log q * Real.log (1 - a * q)| +
                |(1 / 2 : ℝ) * (Real.log (1 - a)) ^ 2| +
                |li2Series (-(a / (1 - a)))| + |li2Series a| := by
                  simp only [abs_neg]
    _ ≤ (48 / 19 : ℝ) * η + (648 / 289 : ℝ) * ρ ^ 2 +
        ((486 / 289 : ℝ) * ρ ^ 2 *
          (|Real.log ρ| + (81 / 32 : ℝ) * ρ)) +
        (9 / 8 : ℝ) * ρ ^ 2 + (8 / 7 : ℝ) * ρ + (16 / 15 : ℝ) * ρ := by
      linarith
    _ = (48 / 19 : ℝ) * η + (232 / 105 : ℝ) * ρ +
        ((648 / 289 : ℝ) + (9 / 8 : ℝ)) * ρ ^ 2 +
        (486 / 289 : ℝ) * ρ ^ 2 *
          (|Real.log ρ| + (81 / 32 : ℝ) * ρ) := by ring

end GppScalarBoxSpecialFunctionRemainder

#print axioms GppScalarBoxSpecialFunctionRemainder.abs_li2Series_a_le_rho
#print axioms GppScalarBoxSpecialFunctionRemainder.abs_li2Series_neg_a_div_one_sub_a_le_rho
#print axioms GppScalarBoxSpecialFunctionRemainder.lower_endpoint_li2_pair_le
#print axioms GppScalarBoxSpecialFunctionRemainder.abs_specialRemainder_le
