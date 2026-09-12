/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Ring.GeomSum

/-!
# Weierstrass elementary factors

This file defines the Weierstrass elementary factors

  `E p z = (1 - z) * exp (z + z^2/2 + ⋯ + z^p/p)`

and proves the fundamental estimate

  `‖1 - E p z‖ ≤ ‖z‖ ^ (p + 1)`   for `‖z‖ ≤ 1`.

These are the building blocks of the Weierstrass product theorem and of Hadamard's
factorisation theorem: `E p` is an entire function whose only zero is a simple zero at `1`,
and the estimate is exactly what makes an infinite product `∏ E p (z / aₙ)` converge
locally uniformly once `∑ ‖aₙ‖⁻¹ ^ (p + 1) < ∞`.

## Main definitions

* `Complex.logOneSubPartialSum p z` : the partial sum `∑_{k=1}^{p} z^k / k` of the power series
  of `-log (1 - z)`.
* `Complex.weierstrassFactor p z` : the elementary factor `E p z`.

## Main results

* `Complex.hasDerivAt_weierstrassFactor` : `E p` is entire with `(E p)' z = -z^p * exp (Sₚ z)`.
  This single clean formula is the source of every estimate below.
* `Complex.one_sub_weierstrassFactor_eq_integral` : the integral representation
  `1 - E p z = z^(p+1) * ∫ t in 0..1, t^p * exp (Sₚ (t * z))`.
* `Complex.norm_one_sub_weierstrassFactor_le` : the fundamental estimate
  `‖1 - E p z‖ ≤ ‖z‖^(p+1)` on the closed unit disc.

## Implementation notes

The usual textbook proof of the fundamental estimate argues that `1 - E p z` has nonnegative
Taylor coefficients (because `(E p)' z = -z^p exp (Sₚ z)` and `exp ∘ Sₚ` has nonnegative
coefficients), that these coefficients sum to `1 - E p 1 = 1`, and that the series starts in
degree `p + 1`.

We avoid formal power series entirely. Integrating `(E p)'` along the segment `[0, z]` gives

  `1 - E p z = z^(p+1) * ∫ t in 0..1, t^p * exp (Sₚ (t * z))`,

and `Re (Sₚ w) ≤ Sₚ ‖w‖` bounds the complex integral by the real one, so

  `‖1 - E p z‖ ≤ ‖z‖^(p+1) * J ‖z‖`,  where  `J r = ∫ t in 0..1, t^p * rexp (Sₚ (t * r))`.

The same representation at `z = 1`, where `E p 1 = 0`, evaluates `J 1 = 1` outright, and `J` is
monotone because its integrand is. This replaces the coefficient-positivity argument by two
monotonicity steps and one evaluation.
-/

open Finset MeasureTheory intervalIntegral

namespace Complex

/-- The `p`-th partial sum `∑_{k=1}^{p} z^k / k` of the power series of `-log (1 - z)`. -/
noncomputable def logOneSubPartialSum (p : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ range p, z ^ (k + 1) / (k + 1)

/-- The Weierstrass elementary factor `E p z = (1 - z) * exp (∑_{k=1}^{p} z^k / k)`. -/
noncomputable def weierstrassFactor (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (logOneSubPartialSum p z)

end Complex

namespace Real

/-- The real `p`-th partial sum `∑_{k=1}^{p} x^k / k`. -/
noncomputable def logOneSubPartialSum (p : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range p, x ^ (k + 1) / (k + 1)

end Real

namespace Complex

@[simp]
theorem ofReal_logOneSubPartialSum (p : ℕ) (x : ℝ) :
    ((Real.logOneSubPartialSum p x : ℝ) : ℂ) = logOneSubPartialSum p (x : ℂ) := by
  simp [Real.logOneSubPartialSum, logOneSubPartialSum]

@[simp]
theorem logOneSubPartialSum_zero (p : ℕ) : logOneSubPartialSum p 0 = 0 := by
  simp [logOneSubPartialSum]

@[simp]
theorem weierstrassFactor_zero (p : ℕ) : weierstrassFactor p 0 = 1 := by
  simp [weierstrassFactor]

@[simp]
theorem weierstrassFactor_one (p : ℕ) : weierstrassFactor p 1 = 0 := by
  simp [weierstrassFactor]

theorem weierstrassFactor_zero_eq (z : ℂ) : weierstrassFactor 0 z = 1 - z := by
  simp [weierstrassFactor, logOneSubPartialSum]

/-- `E p` vanishes only at `1`. -/
theorem weierstrassFactor_ne_zero {p : ℕ} {z : ℂ} (hz : z ≠ 1) : weierstrassFactor p z ≠ 0 := by
  refine mul_ne_zero (sub_ne_zero.2 (Ne.symm hz)) (exp_ne_zero _)

@[simp]
theorem weierstrassFactor_eq_zero_iff {p : ℕ} {z : ℂ} : weierstrassFactor p z = 0 ↔ z = 1 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  by_contra hz
  exact weierstrassFactor_ne_zero hz h

/-! ### Derivative -/

theorem hasDerivAt_logOneSubPartialSum (p : ℕ) (z : ℂ) :
    HasDerivAt (logOneSubPartialSum p) (∑ k ∈ range p, z ^ k) z := by
  have key : ∀ k ∈ range p,
      HasDerivAt (fun w : ℂ => w ^ (k + 1) / ((k : ℂ) + 1)) (z ^ k) z := by
    intro k _
    have hk : ((k : ℂ) + 1) ≠ 0 := by
      exact_mod_cast Nat.cast_add_one_ne_zero (R := ℂ) k
    have h := (hasDerivAt_pow (k + 1) z).div_const ((k : ℂ) + 1)
    have hrw : ((k + 1 : ℕ) : ℂ) * z ^ (k + 1 - 1) / ((k : ℂ) + 1) = z ^ k := by
      push_cast
      field_simp
    exact hrw ▸ h
  have h := HasDerivAt.sum key
  have heq : (∑ k ∈ range p, fun w : ℂ => w ^ (k + 1) / ((k : ℂ) + 1))
      = logOneSubPartialSum p := by
    funext w
    simp [logOneSubPartialSum, Finset.sum_apply]
  exact heq ▸ h

theorem differentiable_logOneSubPartialSum (p : ℕ) : Differentiable ℂ (logOneSubPartialSum p) :=
  fun z => (hasDerivAt_logOneSubPartialSum p z).differentiableAt

/-- The defining differential identity: `(E p)' z = -z^p * exp (Sₚ z)`. The partial sum `Sₚ`
was chosen precisely so that the pole of `(log (1 - z))'` cancels against the geometric sum,
leaving a single monomial. -/
theorem hasDerivAt_weierstrassFactor (p : ℕ) (z : ℂ) :
    HasDerivAt (weierstrassFactor p) (-(z ^ p * exp (logOneSubPartialSum p z))) z := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub 1
  have h2 : HasDerivAt (fun w : ℂ => exp (logOneSubPartialSum p w))
      (exp (logOneSubPartialSum p z) * ∑ k ∈ range p, z ^ k) z :=
    (hasDerivAt_logOneSubPartialSum p z).cexp
  have h := h1.mul h2
  have hg : (∑ k ∈ range p, z ^ k) * (1 - z) = 1 - z ^ p := geom_sum_mul_neg z p
  refine h.congr_deriv ?_
  have : (-1 : ℂ) * exp (logOneSubPartialSum p z)
      + (1 - z) * (exp (logOneSubPartialSum p z) * ∑ k ∈ range p, z ^ k)
      = -(z ^ p * exp (logOneSubPartialSum p z)) := by
    linear_combination (exp (logOneSubPartialSum p z)) * hg
  exact this

theorem differentiable_weierstrassFactor (p : ℕ) : Differentiable ℂ (weierstrassFactor p) :=
  fun z => (hasDerivAt_weierstrassFactor p z).differentiableAt

/-! ### The integral representation -/

theorem continuous_logOneSubPartialSum (p : ℕ) : Continuous (logOneSubPartialSum p) := by
  unfold logOneSubPartialSum
  fun_prop

theorem _root_.Real.continuous_logOneSubPartialSum (p : ℕ) :
    Continuous (Real.logOneSubPartialSum p) := by
  unfold Real.logOneSubPartialSum
  fun_prop

/-- `Sₚ` is monotone on `[0, ∞)`: all of its coefficients are nonnegative. -/
theorem _root_.Real.logOneSubPartialSum_le_logOneSubPartialSum (p : ℕ) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) : Real.logOneSubPartialSum p x ≤ Real.logOneSubPartialSum p y := by
  refine Finset.sum_le_sum fun k _ => ?_
  gcongr

/-- The real part of `Sₚ w` is dominated by `Sₚ ‖w‖`, because `Re (wᵏ) ≤ ‖w‖ᵏ` termwise and the
coefficients of `Sₚ` are nonnegative. This is the one inequality that replaces the classical
power-series positivity argument. -/
theorem re_logOneSubPartialSum_le (p : ℕ) (w : ℂ) :
    (logOneSubPartialSum p w).re ≤ Real.logOneSubPartialSum p ‖w‖ := by
  rw [logOneSubPartialSum, Complex.re_sum, Real.logOneSubPartialSum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hcast : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [hcast, Complex.div_ofReal_re]
  have h2 : (w ^ (k + 1)).re ≤ ‖w‖ ^ (k + 1) := by
    calc (w ^ (k + 1)).re ≤ ‖w ^ (k + 1)‖ := Complex.re_le_norm _
      _ = ‖w‖ ^ (k + 1) := by rw [norm_pow]
  gcongr

/-- The kernel appearing in the integral representation of `1 - E p z`. -/
noncomputable def weierstrassKernel (p : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ p * exp (logOneSubPartialSum p (t * z))

/-- The real majorant of `weierstrassKernel`, and the whole content of the estimate. -/
noncomputable def weierstrassIntegral (p : ℕ) (r : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, t ^ p * Real.exp (Real.logOneSubPartialSum p (t * r))

theorem continuous_weierstrassKernel (p : ℕ) (z : ℂ) : Continuous (weierstrassKernel p z) := by
  unfold weierstrassKernel
  exact (continuous_ofReal.pow p).mul
    (((continuous_logOneSubPartialSum p).comp (continuous_ofReal.mul continuous_const)).cexp)

theorem continuous_weierstrassKernelReal (p : ℕ) (r : ℝ) :
    Continuous (fun t : ℝ => t ^ p * Real.exp (Real.logOneSubPartialSum p (t * r))) :=
  (continuous_pow p).mul
    (((Real.continuous_logOneSubPartialSum p).comp (continuous_id.mul continuous_const)).rexp)

/-- **Integral representation.** Integrating `(E p)' w = -wᵖ exp (Sₚ w)` along the segment from
`0` to `z` gives
`1 - E p z = z^(p+1) * ∫ t in 0..1, tᵖ exp (Sₚ (t z))`. -/
theorem one_sub_weierstrassFactor_eq_integral (p : ℕ) (z : ℂ) :
    1 - weierstrassFactor p z = z ^ (p + 1) * ∫ t in (0:ℝ)..1, weierstrassKernel p z t := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => weierstrassFactor p ((s : ℂ) * z))
      (-(z ^ (p + 1) * weierstrassKernel p z t)) t := by
    intro t
    have hinner : HasDerivAt (fun w : ℂ => w * z) z (t : ℂ) := by
      simpa using (hasDerivAt_id ((t : ℂ))).mul_const z
    have hcomp := (hasDerivAt_weierstrassFactor p ((t : ℂ) * z)).comp (t : ℂ) hinner
    simp only [Function.comp_def] at hcomp
    refine hcomp.comp_ofReal.congr_deriv ?_
    simp only [weierstrassKernel]
    ring
  have hint : IntervalIntegrable (fun t : ℝ => -(z ^ (p + 1) * weierstrassKernel p z t))
      MeasureTheory.volume 0 1 :=
    (((continuous_weierstrassKernel p z).const_mul _).neg).intervalIntegrable 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hFTC
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul,
    weierstrassFactor_zero] at hFTC
  linear_combination hFTC

/-! ### The fundamental estimate -/

/-- At `r = 1` the integral is exactly `1`, because `E p 1 = 0`. This is the step that in the
classical proof reads "the Taylor coefficients of `1 - E p` sum to `1`". -/
theorem weierstrassIntegral_one (p : ℕ) : weierstrassIntegral p 1 = 1 := by
  have h := one_sub_weierstrassFactor_eq_integral p 1
  rw [weierstrassFactor_one] at h
  have hker : ∀ t : ℝ, weierstrassKernel p 1 t
      = ((t ^ p * Real.exp (Real.logOneSubPartialSum p (t * 1)) : ℝ) : ℂ) := by
    intro t
    simp only [weierstrassKernel, mul_one, ofReal_mul, ofReal_pow, ofReal_exp,
      ofReal_logOneSubPartialSum]
  simp only [hker, intervalIntegral.integral_ofReal, one_pow, one_mul, sub_zero] at h
  simpa [weierstrassIntegral] using h.symm

/-- The integral is monotone in `r`, since its integrand is. -/
theorem weierstrassIntegral_le_one (p : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    weierstrassIntegral p r ≤ 1 := by
  rw [← weierstrassIntegral_one p]
  simp only [weierstrassIntegral]
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_weierstrassKernelReal p r).intervalIntegrable 0 1)
    ((continuous_weierstrassKernelReal p 1).intervalIntegrable 0 1) ?_
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have hmono : Real.logOneSubPartialSum p (t * r) ≤ Real.logOneSubPartialSum p (t * 1) :=
    Real.logOneSubPartialSum_le_logOneSubPartialSum p (by positivity) (by nlinarith)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hmono) (by positivity)

/-- The complex integral is dominated by its real counterpart at `r = ‖z‖`. -/
theorem norm_integral_weierstrassKernel_le (p : ℕ) (z : ℂ) :
    ‖∫ t in (0:ℝ)..1, weierstrassKernel p z t‖ ≤ weierstrassIntegral p ‖z‖ := by
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by norm_num)) ?_
  simp only [weierstrassIntegral]
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_weierstrassKernel p z).norm.intervalIntegrable 0 1)
    ((continuous_weierstrassKernelReal p ‖z‖).intervalIntegrable 0 1) ?_
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have hnorm : ‖weierstrassKernel p z t‖
      = t ^ p * Real.exp ((logOneSubPartialSum p ((t : ℂ) * z)).re) := by
    simp [weierstrassKernel, Complex.norm_exp, abs_of_nonneg ht0]
  rw [hnorm]
  have hre : (logOneSubPartialSum p ((t : ℂ) * z)).re
      ≤ Real.logOneSubPartialSum p (t * ‖z‖) := by
    have h := re_logOneSubPartialSum_le p ((t : ℂ) * z)
    simpa [abs_of_nonneg ht0] using h
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hre) (by positivity)

/-- **The fundamental estimate for Weierstrass elementary factors.**

On the closed unit disc, `E p` differs from `1` by at most `‖z‖^(p+1)`. This is what makes the
Weierstrass product `∏ E p (z / aₙ)` converge locally uniformly as soon as
`∑ ‖aₙ‖⁻¹^(p+1) < ∞`. -/
theorem norm_one_sub_weierstrassFactor_le (p : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖1 - weierstrassFactor p z‖ ≤ ‖z‖ ^ (p + 1) := by
  rw [one_sub_weierstrassFactor_eq_integral, norm_mul, norm_pow]
  have hbound : ‖∫ t in (0:ℝ)..1, weierstrassKernel p z t‖ ≤ 1 :=
    le_trans (norm_integral_weierstrassKernel_le p z)
      (weierstrassIntegral_le_one p (norm_nonneg z) hz)
  calc ‖z‖ ^ (p + 1) * ‖∫ t in (0:ℝ)..1, weierstrassKernel p z t‖
      ≤ ‖z‖ ^ (p + 1) * 1 := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ‖z‖ ^ (p + 1) := mul_one _

end Complex
