/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; identity from Codex / GPT, audited by Turbo)
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Stieltjes summation by parts for the von Mangoldt function

With `ψ x = Σ_{n ≤ x} Λ(n)` (`Chebyshev.psi`) and `D x = ψ x − x + 1`, the step discrepancy of the
least common multiple, `ψ x = log lcm(1, …, ⌊x⌋)`, the measure `dD = Σ Λ(n) δ_n − dx` pairs with a
`C¹` weight `w` by integration by parts:

* `lambda_stieltjes_identity`: for `w : ℝ → ℝ` of class `C¹` and real `N ≥ 1`,
  `Σ_{1 ≤ n ≤ N} Λ(n) w(n) − ∫₁ᴺ w = D(N) w(N) − ∫₁ᴺ D(x) w′(x) dx`.
* `lambda_stieltjes_compact`: when `w` has compact support inside `[1, N]` the boundary term
  vanishes, `Σ_{1 ≤ n ≤ N} Λ(n) w(n) − ∫₁ᴺ w = − ∫₁ᴺ D(x) w′(x) dx`; this is the form used in the
  `a = 2` undamping identity of the LCM experiment.

The proof is Abel summation for `Λ` (`sum_mul_eq_sub_integral_mul₀`), integration by parts for
`∫ w` against `x`, and the fundamental theorem of calculus for `∫ w′`; the terms `w(1)` and
`∫ w′` cancel, so no support or vanishing hypothesis at `1` enters the main identity.
-/

open Finset MeasureTheory intervalIntegral ArithmeticFunction

namespace GppLambdaStieltjes

/-- The step discrepancy `D x = ψ x − x + 1`. -/
noncomputable def D (x : ℝ) : ℝ := Chebyshev.psi x - x + 1

/-- The sum `Σ_{0 ≤ k ≤ m} w(k) Λ(k)` is `Σ_{1 ≤ n ≤ m} Λ(n) w(n)`, since `Λ 0 = 0`. -/
theorem sum_Icc_zero_eq (w : ℝ → ℝ) (m : ℕ) :
    ∑ k ∈ Icc 0 m, w k * Λ k = ∑ n ∈ Icc 1 m, Λ n * w n := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  have h : Finset.Ioc 0 m = Finset.Icc 1 m := by ext; simp; omega
  rw [h]
  simp only [ArithmeticFunction.map_zero, mul_zero, zero_add]
  exact Finset.sum_congr rfl fun n _ => mul_comm _ _

/-- **Stieltjes summation by parts for `Λ`.** For `w` of class `C¹` and real `N ≥ 1`,
`Σ_{1 ≤ n ≤ N} Λ(n) w(n) − ∫₁ᴺ w = D(N) w(N) − ∫₁ᴺ D(x) w′(x) dx`. -/
theorem lambda_stieltjes_identity {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w) {N : ℝ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 ⌊N⌋₊, Λ n * w n - ∫ x in (1 : ℝ)..N, w x =
      D N * w N - ∫ x in (1 : ℝ)..N, D x * deriv w x := by
  have hdiff : ∀ t, DifferentiableAt ℝ w t := fun t => hw.differentiable (by norm_num) t
  have hcont' : Continuous (deriv w) := hw.continuous_deriv (by norm_num)
  have hder : ∀ t, HasDerivAt w (deriv w t) t := fun t => (hdiff t).hasDerivAt
  have hint' : IntervalIntegrable (deriv w) volume 1 N := hcont'.intervalIntegrable _ _
  -- Abel summation for the coefficients `Λ`
  have hAbel := sum_mul_eq_sub_integral_mul₀ (fun n : ℕ => (Λ n : ℝ)) (by simp) N
    (fun t _ => hdiff t) hcont'.integrableOn_Icc
  simp only [← Chebyshev.psi_eq_sum_Icc] at hAbel
  rw [sum_Icc_zero_eq, ← intervalIntegral.integral_of_le hN] at hAbel
  have hψ : IntervalIntegrable Chebyshev.psi volume 1 N := Chebyshev.psi_mono.intervalIntegrable
  have hψw : IntervalIntegrable (fun x => deriv w x * Chebyshev.psi x) volume 1 N :=
    hψ.continuousOn_mul hcont'.continuousOn
  have hxw : IntervalIntegrable (fun x => deriv w x * x) volume 1 N :=
    (hcont'.mul continuous_id).intervalIntegrable _ _
  -- integration by parts: `∫ w = N w(N) − w(1) − ∫ x w′`
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 1) (b := N) (u := w)
    (u' := deriv w) (v := fun x => x) (v' := fun _ => (1 : ℝ)) (fun x _ => hder x)
    (fun x _ => hasDerivAt_id x) hint' intervalIntegrable_const
  simp only [mul_one] at hIBP
  -- fundamental theorem of calculus: `∫ w′ = w(N) − w(1)`
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x) hint'
  -- split `D w′`
  have hsplit : ∫ x in (1 : ℝ)..N, D x * deriv w x =
      (∫ x in (1 : ℝ)..N, deriv w x * Chebyshev.psi x) - (∫ x in (1 : ℝ)..N, deriv w x * x) +
        ∫ x in (1 : ℝ)..N, deriv w x := by
    have h : (fun x => D x * deriv w x) =
        fun x => (deriv w x * Chebyshev.psi x - deriv w x * x) + deriv w x := by
      funext x; simp only [D]; ring
    rw [h, intervalIntegral.integral_add (hψw.sub hxw) hint',
      intervalIntegral.integral_sub hψw hxw]
  rw [hsplit]
  simp only [D]
  linear_combination hAbel - hIBP + hFTC

/-- **Boundary term gone.** If `w(N) = 0` the identity reads
`Σ_{1 ≤ n ≤ N} Λ(n) w(n) − ∫₁ᴺ w = − ∫₁ᴺ D(x) w′(x) dx`. -/
theorem lambda_stieltjes_of_eq_zero {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w) {N : ℝ} (hN : 1 ≤ N)
    (hwN : w N = 0) :
    ∑ n ∈ Icc 1 ⌊N⌋₊, Λ n * w n - ∫ x in (1 : ℝ)..N, w x =
      -∫ x in (1 : ℝ)..N, D x * deriv w x := by
  have h := lambda_stieltjes_identity hw hN
  rw [hwN, mul_zero, zero_sub] at h
  exact h

/-- **Compact support.** For `w` of class `C¹` with compact support, the boundary term vanishes for
all large `N`, and `Σ_{1 ≤ n ≤ N} Λ(n) w(n) − ∫₁ᴺ w = − ∫₁ᴺ D(x) w′(x) dx`. -/
theorem lambda_stieltjes_compact {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w) (hc : HasCompactSupport w) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∑ n ∈ Icc 1 ⌊N⌋₊, Λ n * w n - ∫ x in (1 : ℝ)..N, w x =
        -∫ x in (1 : ℝ)..N, D x * deriv w x := by
  obtain ⟨R, hR⟩ := hc.isCompact.bddAbove
  refine ⟨max 1 (R + 1), le_max_left _ _, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hwN : w N = 0 := by
    by_contra h
    have hmem : N ∈ tsupport w := subset_tsupport _ h
    have := hR hmem
    linarith [le_max_right 1 (R + 1)]
  exact lambda_stieltjes_of_eq_zero hw hN1 hwN

end GppLambdaStieltjes

#print axioms GppLambdaStieltjes.lambda_stieltjes_identity
#print axioms GppLambdaStieltjes.lambda_stieltjes_of_eq_zero
#print axioms GppLambdaStieltjes.lambda_stieltjes_compact
