/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Golden Eye)
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Elementary Bose-type integrals and a Bernoulli bound

Mathlib-style lemmas staged for upstreaming (see `README.md`).

* `Real.hasDerivAt_log_one_sub_exp_neg`: `d/dx log(1 - e^{-x}) = 1/(e^x - 1)` for `x > 0`.
* `Real.integral_Ioi_one_div_exp_sub_one`: `∫_{(a,∞)} 1/(e^x - 1) dx = -log(1 - e^{-a})`, `a > 0`.
* `Real.div_exp_sub_one_le`: `x/(e^x - 1) ≤ 1 - x/2 + x²/12` for `x > 0` (truncated Bernoulli
  generating function), and `Real.div_exp_sub_one_le_one`: `x/(e^x - 1) ≤ 1`.
* `Real.integrableOn_Ioc_div_exp_sub_one` and `Real.setIntegral_Ioc_div_exp_sub_one_le`:
  `∫_{(0,b]} x/(e^x - 1) dx ≤ b - b²/4 + b³/36` for `0 ≤ b`.
-/

open Set Filter Topology MeasureTheory

namespace Real

theorem one_div_exp_sub_one_pos {x : ℝ} (hx : 0 < x) : 0 < 1 / (exp x - 1) :=
  one_div_pos.2 (sub_pos.2 (one_lt_exp_iff.2 hx))

theorem hasDerivAt_log_one_sub_exp_neg {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => log (1 - exp (-t))) (1 / (exp x - 1)) x := by
  have hlt : exp (-x) < 1 := exp_lt_one_iff.2 (neg_lt_zero.2 hx)
  have hne : 1 - exp (-x) ≠ 0 := (sub_pos.2 hlt).ne'
  have h1 : HasDerivAt (fun t => 1 - exp (-t)) (exp (-x)) x := by
    exact (((hasDerivAt_neg x).exp).const_sub 1).congr_deriv (by ring)
  refine (h1.log hne).congr_deriv ?_
  have hex : exp x - 1 ≠ 0 := (sub_pos.2 (one_lt_exp_iff.2 hx)).ne'
  rw [exp_neg] at hne ⊢
  have hE : exp x ≠ 0 := (exp_pos x).ne'
  field_simp

theorem tendsto_log_one_sub_exp_neg :
    Tendsto (fun t : ℝ => log (1 - exp (-t))) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => 1 - exp (-t)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub tendsto_exp_neg_atTop_nhds_zero
  rw [sub_zero] at h
  have := ((continuousAt_log one_ne_zero).tendsto).comp h
  rw [log_one] at this
  exact this

theorem integrableOn_Ioi_one_div_exp_sub_one {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x => 1 / (exp x - 1)) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg
    (hasDerivAt_log_one_sub_exp_neg ha).continuousAt.continuousWithinAt
    (fun _ hx => hasDerivAt_log_one_sub_exp_neg (ha.trans hx))
    (fun _ hx => (one_div_exp_sub_one_pos (ha.trans hx)).le) tendsto_log_one_sub_exp_neg

theorem integral_Ioi_one_div_exp_sub_one {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi a, 1 / (exp x - 1) = -log (1 - exp (-a)) := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg
    (hasDerivAt_log_one_sub_exp_neg ha).continuousAt.continuousWithinAt
    (fun x hx => hasDerivAt_log_one_sub_exp_neg (ha.trans hx))
    (fun _ hx => (one_div_exp_sub_one_pos (ha.trans hx)).le) tendsto_log_one_sub_exp_neg,
    zero_sub]

/-- Fifth-order Taylor lower bound for `exp` on `[0, ∞)`. -/
theorem quintic_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 ≤ exp x := by
  have h := sum_le_exp_of_nonneg hx 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The truncated Bernoulli bound `x/(e^x - 1) ≤ 1 - x/2 + x²/12` for `x > 0`. -/
theorem div_exp_sub_one_le {x : ℝ} (hx : 0 < x) :
    x / (exp x - 1) ≤ 1 - x / 2 + x ^ 2 / 12 := by
  have hT := quintic_le_exp_of_nonneg hx.le
  have hd : 0 < exp x - 1 := sub_pos.2 (one_lt_exp_iff.2 hx)
  have hp : 0 < 1 - x / 2 + x ^ 2 / 12 := by nlinarith [sq_nonneg (x - 3)]
  rw [div_le_iff₀ hd]
  have hq : 0 ≤ x ^ 5 * (2 - x + x ^ 2) := by
    have : 0 < 2 - x + x ^ 2 := by nlinarith [sq_nonneg (x - 1 / 2)]
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hT hp.le]

theorem div_exp_sub_one_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x / (exp x - 1) :=
  div_nonneg hx (sub_nonneg.2 (one_le_exp hx))

theorem div_exp_sub_one_le_one {x : ℝ} (hx : 0 < x) : x / (exp x - 1) ≤ 1 := by
  rw [div_le_one (sub_pos.2 (one_lt_exp_iff.2 hx))]
  linarith [add_one_le_exp x]

theorem continuousOn_Ioi_div_exp_sub_one :
    ContinuousOn (fun x : ℝ => x / (exp x - 1)) (Ioi 0) :=
  continuousOn_id.div (continuous_exp.sub continuous_const).continuousOn
    (fun _ hx => (sub_pos.2 (one_lt_exp_iff.2 hx)).ne')

theorem integrableOn_Ioc_div_exp_sub_one (b : ℝ) :
    IntegrableOn (fun x : ℝ => x / (exp x - 1)) (Ioc 0 b) := by
  refine Integrable.mono' (integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne)
    ((continuousOn_Ioi_div_exp_sub_one.mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (div_exp_sub_one_nonneg hx.1.le)]
  exact div_exp_sub_one_le_one hx.1

theorem setIntegral_Ioc_div_exp_sub_one_le {b : ℝ} (hb : 0 ≤ b) :
    ∫ x in Ioc 0 b, x / (exp x - 1) ≤ b - b ^ 2 / 4 + b ^ 3 / 36 := by
  have hpoly : IntegrableOn (fun x : ℝ => 1 - x / 2 + x ^ 2 / 12) (Ioc 0 b) :=
    (by fun_prop : Continuous fun x : ℝ => 1 - x / 2 + x ^ 2 / 12).integrableOn_Ioc
  calc ∫ x in Ioc 0 b, x / (exp x - 1)
      ≤ ∫ x in Ioc 0 b, (1 - x / 2 + x ^ 2 / 12) :=
        setIntegral_mono_on (integrableOn_Ioc_div_exp_sub_one b) hpoly measurableSet_Ioc
          fun x hx => div_exp_sub_one_le hx.1
    _ = b - b ^ 2 / 4 + b ^ 3 / 36 := by
        rw [← intervalIntegral.integral_of_le hb,
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (f := fun x : ℝ => x - x ^ 2 / 4 + x ^ 3 / 36)
            (fun x _ => by
              have := (((hasDerivAt_id' x).sub ((hasDerivAt_pow 2 x).div_const 4)).add
                ((hasDerivAt_pow 3 x).div_const 36))
              convert this using 1
              · funext y; simp only [Pi.add_apply, Pi.sub_apply]
              · norm_num; ring)
            ((by fun_prop : Continuous fun x : ℝ => 1 - x / 2 + x ^ 2 / 12).intervalIntegrable
              _ _)]
        ring

end Real
