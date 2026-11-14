/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The sharp Taylor remainder of `exp (I y)`, and Fourier transforms with vanishing moments

For real `y`, the degree-`d` Taylor remainder of `y ↦ exp (I y)` satisfies
`‖exp (I y) - Σ_{m<d} (I y)^m / m!‖ ≤ |y|^d / d!`. Mathlib's general complex bounds carry an extra
factor `exp ‖x‖` or need `‖x‖ ≤ 1`; on the imaginary axis neither is needed, and the factorial is the
whole point when `d` is large.

As a consequence, if `f` on `[-ℓ, ℓ]` has vanishing moments of order `< d`, its Fourier transform is
`O(|r|^d)` near `0`, with the explicit constant `ℓ^d / d! · ∫|f|`. This is the bound that controls
the high-mode tail of a Legendre (or any moment-orthogonal) expansion in a computer-assisted Gram
certificate.

## Main results

* `Complex.hasDerivAt_expTaylor_I`: the derivative of the degree-`d+1` Taylor polynomial of
  `exp (I t)` is `I` times the degree-`d` one.
* `Complex.norm_exp_I_mul_sub_taylor_le`: `‖exp (I y) - Σ_{m<d} (I y)^m/m!‖ ≤ |y|^d / d!`.
* `Complex.norm_integral_mul_exp_I_sub_moments_le`: `‖∫ f e^{irx} - Σ_{m<d} (ir)^m/m! ∫ f x^m‖ ≤
  (|r| ℓ)^d / d! * ∫ ‖f‖` on `[-ℓ, ℓ]`, the transform by its moments.
* `Complex.norm_integral_mul_exp_I_le_of_moments`: for `f` interval-integrable on `[-ℓ, ℓ]` with
  `∫ f x * x^k = 0` for all `k < d`, `‖∫ f x * exp (I r x)‖ ≤ (|r| ℓ)^d / d! * ∫ ‖f x‖`.
-/

open Finset intervalIntegral MeasureTheory

namespace Complex

/-- The degree-`< d` Taylor polynomial of `t ↦ exp (I t)` at `0`. -/
noncomputable def expTaylorI (d : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ range d, (I * t) ^ m / m.factorial

@[simp] theorem expTaylorI_zero (t : ℝ) : expTaylorI 0 t = 0 := by simp [expTaylorI]

theorem expTaylorI_succ (d : ℕ) (t : ℝ) :
    expTaylorI (d + 1) t = expTaylorI d t + (I * t) ^ d / d.factorial := by
  simp [expTaylorI, sum_range_succ]

theorem expTaylorI_at_zero (d : ℕ) : expTaylorI (d + 1) 0 = 1 := by
  induction d with
  | zero => simp [expTaylorI]
  | succ n ih => rw [expTaylorI_succ, ih]; simp

/-- The derivative of the monomial `(I t)^(d+1) / (d+1)!` is `I (I t)^d / d!`. -/
theorem hasDerivAt_monomial_I (d : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (I * s) ^ (d + 1) / ((d + 1).factorial : ℂ))
      (I * ((I * t) ^ d / d.factorial)) t := by
  have h1 : HasDerivAt (fun s : ℝ => I * (s : ℂ)) I t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).const_mul I
  have h2 := (h1.pow (d + 1)).div_const ((d + 1).factorial : ℂ)
  refine h2.congr_deriv ?_
  have hf : (d.factorial : ℂ) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
  rw [Nat.factorial_succ, Nat.add_sub_cancel]
  push_cast
  field_simp

/-- **The derivative of the Taylor polynomial.** `d/dt Σ_{m<d+1} (I t)^m/m! = I Σ_{m<d} (I t)^m/m!`. -/
theorem hasDerivAt_expTaylorI (d : ℕ) (t : ℝ) :
    HasDerivAt (expTaylorI (d + 1)) (I * expTaylorI d t) t := by
  induction d with
  | zero =>
    have : expTaylorI 1 = fun _ => (1 : ℂ) := by funext s; simp [expTaylorI]
    rw [this]; simpa using hasDerivAt_const t (1 : ℂ)
  | succ n ih =>
    have hfun : expTaylorI (n + 2) =
        fun s => expTaylorI (n + 1) s + (I * s) ^ (n + 1) / ((n + 1).factorial : ℂ) := by
      funext s; rw [expTaylorI_succ]
    rw [hfun, expTaylorI_succ, mul_add]
    exact ih.add (hasDerivAt_monomial_I n t)

theorem continuous_expTaylorI (d : ℕ) : Continuous (expTaylorI d) := by
  unfold expTaylorI
  fun_prop

/-- The remainder `exp (I t) - Σ_{m<d} (I t)^m/m!`. -/
noncomputable def expRemI (d : ℕ) (t : ℝ) : ℂ := exp (I * t) - expTaylorI d t

theorem continuous_expRemI (d : ℕ) : Continuous (expRemI d) := by
  unfold expRemI
  exact (by fun_prop : Continuous fun t : ℝ => exp (I * t)).sub (continuous_expTaylorI d)

theorem hasDerivAt_expRemI (d : ℕ) (t : ℝ) :
    HasDerivAt (expRemI (d + 1)) (I * expRemI d t) t := by
  have he : HasDerivAt (fun s : ℝ => exp (I * s)) (exp (I * t) * I) t := by
    have h1 : HasDerivAt (fun s : ℝ => I * (s : ℂ)) I t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_mul I
    exact h1.cexp
  have h := he.sub (hasDerivAt_expTaylorI d t)
  have heq : exp (I * t) * I - I * expTaylorI d t = I * expRemI d t := by
    unfold expRemI; ring
  rw [heq] at h
  exact h

theorem expRemI_at_zero (d : ℕ) : expRemI (d + 1) 0 = 0 := by
  simp [expRemI, expTaylorI_at_zero]

/-- The remainder is conjugation-symmetric: `R_d(-t) = conj (R_d t)`. -/
theorem expRemI_neg (d : ℕ) (t : ℝ) : expRemI d (-t) = (starRingEnd ℂ) (expRemI d t) := by
  unfold expRemI expTaylorI
  rw [map_sub, ← exp_conj, map_sum]
  congr 1
  · congr 1; simp [conj_ofReal]
  · refine sum_congr rfl fun m _ => ?_
    rw [map_div₀, map_pow, map_mul, conj_I, conj_ofReal, map_natCast]
    push_cast; ring

/-- **The sharp bound for `t ≥ 0`.** -/
theorem norm_expRemI_le_of_nonneg (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖expRemI d t‖ ≤ t ^ d / d.factorial := by
  induction d generalizing t with
  | zero =>
    simp only [expRemI, expTaylorI_zero, sub_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one]
    rw [mul_comm, norm_exp_ofReal_mul_I]
  | succ n ih =>
    have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (expRemI (n + 1)) (I * expRemI n s) s :=
      fun s _ => hasDerivAt_expRemI n s
    have hint : IntervalIntegrable (fun s => I * expRemI n s) volume 0 t :=
      ((continuous_expRemI n).const_mul I).intervalIntegrable 0 t
    have hFTC := integral_eq_sub_of_hasDerivAt hderiv hint
    rw [expRemI_at_zero, sub_zero] at hFTC
    rw [← hFTC]
    have hg : IntervalIntegrable (fun s : ℝ => s ^ n / (n.factorial : ℝ)) volume 0 t :=
      (by fun_prop : Continuous fun s : ℝ => s ^ n / (n.factorial : ℝ)).intervalIntegrable 0 t
    calc ‖∫ s in (0 : ℝ)..t, I * expRemI n s‖
        ≤ ∫ s in (0 : ℝ)..t, s ^ n / (n.factorial : ℝ) := by
          refine norm_integral_le_of_norm_le ht (Filter.Eventually.of_forall fun s hs => ?_) hg
          rw [norm_mul, norm_I, one_mul]
          exact ih hs.1.le
      _ = t ^ (n + 1) / ((n + 1).factorial : ℝ) := by
          rw [intervalIntegral.integral_div, integral_pow, Nat.factorial_succ]
          push_cast
          have : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
          field_simp
          ring

/-- **The sharp Taylor remainder of `exp (I y)`.** For every real `y` and every `d`,
`‖exp (I y) - Σ_{m<d} (I y)^m / m!‖ ≤ |y|^d / d!`. -/
theorem norm_exp_I_mul_sub_taylor_le (d : ℕ) (y : ℝ) :
    ‖exp (I * y) - ∑ m ∈ range d, (I * y) ^ m / m.factorial‖ ≤ |y| ^ d / d.factorial := by
  change ‖expRemI d y‖ ≤ _
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]; exact norm_expRemI_le_of_nonneg d hy
  · have h := norm_expRemI_le_of_nonneg d (neg_nonneg.mpr hy)
    rw [expRemI_neg, RCLike.norm_conj] at h
    rwa [abs_of_nonpos hy]

/-- **The Fourier transform on a window, by moments.** For `f` interval-integrable on `[-ℓ, ℓ]`,
`‖∫ f e^{irx} - Σ_{m<d} (ir)^m/m! ∫ f x^m‖ ≤ (|r| ℓ)^d / d! · ∫ ‖f‖`. -/
theorem norm_integral_mul_exp_I_sub_moments_le {f : ℝ → ℂ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hf : IntervalIntegrable f volume (-ℓ) ℓ) (d : ℕ) (r : ℝ) :
    ‖(∫ x in (-ℓ)..ℓ, f x * exp (I * (r * x : ℝ))) -
        ∑ m ∈ range d, (I * r) ^ m / (m.factorial : ℂ) * ∫ x in (-ℓ)..ℓ, f x * (x : ℂ) ^ m‖ ≤
      (|r| * ℓ) ^ d / d.factorial * ∫ x in (-ℓ)..ℓ, ‖f x‖ := by
  have hle : -ℓ ≤ ℓ := by linarith
  have hmulc : ∀ g : ℝ → ℂ, Continuous g → IntervalIntegrable (fun x => f x * g x) volume (-ℓ) ℓ :=
    fun g hg => hf.mul_continuousOn hg.continuousOn
  have htaylor : ∫ x in (-ℓ)..ℓ, f x * expTaylorI d (r * x) =
      ∑ m ∈ range d, (I * r) ^ m / (m.factorial : ℂ) * ∫ x in (-ℓ)..ℓ, f x * (x : ℂ) ^ m := by
    unfold expTaylorI
    simp_rw [mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · refine sum_congr rfl fun m _ => ?_
      have : (fun x : ℝ => f x * ((I * ((r * x : ℝ) : ℂ)) ^ m / (m.factorial : ℂ))) =
          fun x => ((I * r) ^ m / (m.factorial : ℂ)) * (f x * (x : ℂ) ^ m) := by
        funext x; push_cast; ring
      rw [this, intervalIntegral.integral_const_mul]
    · intro m _
      exact hmulc _ (by fun_prop)
  have hsplit : (∫ x in (-ℓ)..ℓ, f x * exp (I * (r * x : ℝ))) -
      ∑ m ∈ range d, (I * r) ^ m / (m.factorial : ℂ) * ∫ x in (-ℓ)..ℓ, f x * (x : ℂ) ^ m =
      ∫ x in (-ℓ)..ℓ, f x * expRemI d (r * x) := by
    have h1 := intervalIntegral.integral_add (hmulc (fun x => expRemI d (r * x))
      ((continuous_expRemI d).comp (continuous_const.mul continuous_id)))
      (hmulc (fun x => expTaylorI d (r * x))
      ((continuous_expTaylorI d).comp (continuous_const.mul continuous_id)))
    rw [htaylor] at h1
    have e : (fun x => f x * expRemI d (r * x) + f x * expTaylorI d (r * x)) =
        fun x => f x * exp (I * (r * x : ℝ)) := by
      funext x; unfold expRemI; ring
    rw [e] at h1
    rw [h1]; ring
  rw [hsplit]
  have hg : IntervalIntegrable (fun x => (|r| * ℓ) ^ d / d.factorial * ‖f x‖) volume (-ℓ) ℓ :=
    hf.norm.const_mul _
  calc ‖∫ x in (-ℓ)..ℓ, f x * expRemI d (r * x)‖
      ≤ ∫ x in (-ℓ)..ℓ, (|r| * ℓ) ^ d / d.factorial * ‖f x‖ := by
        refine norm_integral_le_of_norm_le hle (Filter.Eventually.of_forall fun x hx => ?_) hg
        rw [norm_mul, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have hR : ‖expRemI d (r * x)‖ ≤ |r * x| ^ d / d.factorial :=
          norm_exp_I_mul_sub_taylor_le d (r * x)
        refine hR.trans ?_
        have hx' : |x| ≤ ℓ := abs_le.mpr ⟨hx.1.le, hx.2⟩
        gcongr
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hx' (abs_nonneg r)
    _ = (|r| * ℓ) ^ d / d.factorial * ∫ x in (-ℓ)..ℓ, ‖f x‖ := by
        rw [intervalIntegral.integral_const_mul]

/-- **Fourier transforms with vanishing moments.** If `f` is interval-integrable on `[-ℓ, ℓ]` and its
moments `∫ f x * x^k` vanish for all `k < d`, then
`‖∫_{-ℓ}^{ℓ} f x * exp (I r x)‖ ≤ (|r| ℓ)^d / d! * ∫_{-ℓ}^{ℓ} ‖f x‖`. -/
theorem norm_integral_mul_exp_I_le_of_moments {f : ℝ → ℂ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hf : IntervalIntegrable f volume (-ℓ) ℓ) {d : ℕ}
    (hmom : ∀ k < d, ∫ x in (-ℓ)..ℓ, f x * (x : ℂ) ^ k = 0) (r : ℝ) :
    ‖∫ x in (-ℓ)..ℓ, f x * exp (I * (r * x : ℝ))‖ ≤
      (|r| * ℓ) ^ d / d.factorial * ∫ x in (-ℓ)..ℓ, ‖f x‖ := by
  have hle : -ℓ ≤ ℓ := by linarith
  -- integrability of `f` times continuous functions
  have hmulc : ∀ g : ℝ → ℂ, Continuous g → IntervalIntegrable (fun x => f x * g x) volume (-ℓ) ℓ :=
    fun g hg => hf.mul_continuousOn hg.continuousOn
  -- the Taylor part integrates to zero
  have htaylor : ∫ x in (-ℓ)..ℓ, f x * expTaylorI d (r * x) = 0 := by
    unfold expTaylorI
    simp_rw [mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · refine sum_eq_zero fun m hm => ?_
      have : (fun x : ℝ => f x * ((I * ((r * x : ℝ) : ℂ)) ^ m / (m.factorial : ℂ))) =
          fun x => ((I * r) ^ m / (m.factorial : ℂ)) * (f x * (x : ℂ) ^ m) := by
        funext x; push_cast; ring
      rw [this, intervalIntegral.integral_const_mul, hmom m (mem_range.mp hm), mul_zero]
    · intro m _
      exact hmulc _ (by fun_prop)
  have hsplit : ∫ x in (-ℓ)..ℓ, f x * exp (I * (r * x : ℝ)) =
      ∫ x in (-ℓ)..ℓ, f x * expRemI d (r * x) := by
    have h1 := intervalIntegral.integral_add (hmulc (fun x => expRemI d (r * x))
      ((continuous_expRemI d).comp (continuous_const.mul continuous_id)))
      (hmulc (fun x => expTaylorI d (r * x))
      ((continuous_expTaylorI d).comp (continuous_const.mul continuous_id)))
    rw [htaylor, add_zero] at h1
    rw [← h1]
    congr 1; funext x; unfold expRemI; ring
  rw [hsplit]
  have hg : IntervalIntegrable (fun x => (|r| * ℓ) ^ d / d.factorial * ‖f x‖) volume (-ℓ) ℓ :=
    hf.norm.const_mul _
  calc ‖∫ x in (-ℓ)..ℓ, f x * expRemI d (r * x)‖
      ≤ ∫ x in (-ℓ)..ℓ, (|r| * ℓ) ^ d / d.factorial * ‖f x‖ := by
        refine norm_integral_le_of_norm_le hle (Filter.Eventually.of_forall fun x hx => ?_) hg
        rw [norm_mul, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have hR : ‖expRemI d (r * x)‖ ≤ |r * x| ^ d / d.factorial :=
          norm_exp_I_mul_sub_taylor_le d (r * x)
        refine hR.trans ?_
        have hx' : |x| ≤ ℓ := abs_le.mpr ⟨hx.1.le, hx.2⟩
        gcongr
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hx' (abs_nonneg r)
    _ = (|r| * ℓ) ^ d / d.factorial * ∫ x in (-ℓ)..ℓ, ‖f x‖ := by
        rw [intervalIntegral.integral_const_mul]

end Complex

#print axioms Complex.norm_exp_I_mul_sub_taylor_le
#print axioms Complex.norm_integral_mul_exp_I_le_of_moments
#print axioms Complex.norm_integral_mul_exp_I_sub_moments_le
