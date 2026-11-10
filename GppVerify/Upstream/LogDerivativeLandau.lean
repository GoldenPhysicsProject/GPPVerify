/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Landau's lemma for the logarithmic derivative

Building blocks for the bound on `f'/f` near a point where `f` is nonzero: a holomorphic
logarithm of a zero-free function on a ball, and the derivative bound that follows from the
Borel–Carathéodory theorem and Cauchy's estimate.
-/

open Complex Metric Set

namespace Complex

/-- **A zero-free holomorphic function on a ball is the exponential of a holomorphic function.** -/
theorem exists_exp_eq_of_ne_zero_ball {g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hg : DifferentiableOn ℂ g (ball c R)) (h0 : ∀ z ∈ ball c R, g z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball c R) ∧ ∀ z ∈ ball c R, g z = exp (h z) := by
  rcases le_or_gt R 0 with hR | hR
  · refine ⟨0, differentiableOn_const _, fun z hz => ?_⟩
    exact absurd hz (by simp [Metric.mem_ball, not_lt.2 (le_trans hR dist_nonneg)])
  have hdiff : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c R) :=
    (hg.deriv isOpen_ball).div hg h0
  obtain ⟨F, hF⟩ := hdiff.isExactOn_ball
  have hFd : DifferentiableOn ℂ F (ball c R) := fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  have hgd : ∀ z ∈ ball c R, HasDerivAt g (deriv g z) z := fun z hz =>
    ((hg z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  set φ : ℂ → ℂ := fun z => g z * exp (-F z) with hφ
  have hφd : ∀ z ∈ ball c R, HasDerivAt φ 0 z := by
    intro z hz
    have h1 := (hgd z hz).mul ((hF z hz).neg.cexp)
    have hgz : g z ≠ 0 := h0 z hz
    refine h1.congr_deriv ?_
    simp only [Pi.neg_apply]
    field_simp
    ring
  have hconst : ∀ z ∈ ball c R, φ z = φ c := by
    intro z hz
    refine isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected ?_ ?_ hz
      (mem_ball_self hR)
    · exact fun w hw => (hφd w hw).differentiableAt.differentiableWithinAt
    · exact fun w hw => (hφd w hw).deriv
  have hφc : φ c ≠ 0 := mul_ne_zero (h0 c (mem_ball_self hR)) (exp_ne_zero _)
  refine ⟨fun z => F z + log (φ c), hFd.add_const _, fun z hz => ?_⟩
  have := hconst z hz
  simp only [hφ] at this hφc
  rw [exp_add, exp_log hφc, ← this]
  rw [mul_left_comm, ← exp_add]
  simp

/-- **Derivative bound from a one-sided bound on the real part** (Borel–Carathéodory + Cauchy).
If `h` is holomorphic on `B(c, R)` and `Re (h z - h c) ≤ M` there, then `‖h'(z)‖ ≤ 24 M / R`
for `‖z - c‖ ≤ R / 2`. -/
theorem norm_deriv_le_of_re_le {h : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hM : 0 < M) (hR : 0 < R)
    (hh : DifferentiableOn ℂ h (ball c R)) (hre : ∀ z ∈ ball c R, (h z - h c).re ≤ M)
    {z : ℂ} (hz : dist z c ≤ R / 2) : ‖deriv h z‖ ≤ 24 * M / R := by
  set k : ℂ → ℂ := fun w => h (c + w) - h c with hk
  have hkd : DifferentiableOn ℂ k (ball 0 R) := by
    refine DifferentiableOn.sub ?_ (differentiableOn_const _)
    refine hh.comp (differentiableOn_const c |>.add differentiableOn_id) ?_
    intro w hw
    simpa [Metric.mem_ball] using hw
  have hkm : Set.MapsTo k (ball 0 R) {w | w.re ≤ M} := by
    intro w hw
    exact hre _ (by simpa [Metric.mem_ball] using hw)
  have hkb : ∀ u : ℂ, ‖u‖ ≤ 3 * R / 4 → ‖h (c + u) - h c‖ ≤ 6 * M := by
    intro u hu
    have hu' : u ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]; linarith
    have := borelCaratheodory_zero hM hkd hkm hR hu' (by simp [hk])
    refine this.trans ?_
    have hden : 0 < R - ‖u‖ := by linarith
    rw [div_le_iff₀ hden]
    nlinarith [norm_nonneg u]
  have hcl : closedBall z (R / 4) ⊆ ball c R := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    have := dist_triangle w z c
    linarith
  have hd : DiffContOnCl ℂ (fun w => h w - h c) (ball z (R / 4)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ (by positivity)]
    exact (hh.mono hcl).sub (differentiableOn_const _)
  have hbound : ∀ w ∈ sphere z (R / 4), ‖(fun w => h w - h c) w‖ ≤ 6 * M := by
    intro w hw
    rw [mem_sphere_iff_norm] at hw
    have := hkb (w - c) (by
      have h1 : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := norm_sub_le_norm_sub_add_norm_sub w z c
      have h2 : ‖z - c‖ ≤ R / 2 := by simpa [dist_eq_norm] using hz
      linarith)
    simpa using this
  have := norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < R / 4) hd hbound
  rw [deriv_sub_const] at this
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

end Complex
