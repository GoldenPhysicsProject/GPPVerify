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
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Calculus.LogDeriv

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

/-- The logarithmic derivative of the canonical (Blaschke) factor at a point `z ≠ w` where the
numerator does not vanish. -/
theorem logDeriv_canonicalFactor {R : ℝ} {w z : ℂ} (hR : R ≠ 0) (hzw : z ≠ w)
    (hnum : (R : ℂ) ^ 2 - (starRingEnd ℂ) w * z ≠ 0) :
    logDeriv (canonicalFactor R w) z =
      -(starRingEnd ℂ) w / ((R : ℂ) ^ 2 - (starRingEnd ℂ) w * z) - 1 / (z - w) := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hnum_d : HasDerivAt (fun x : ℂ => (R : ℂ) ^ 2 - (starRingEnd ℂ) w * x)
      (-(starRingEnd ℂ) w) z := by
    simpa using ((hasDerivAt_id z).const_mul ((starRingEnd ℂ) w)).const_sub ((R : ℂ) ^ 2)
  have hden_d : HasDerivAt (fun x : ℂ => (R : ℂ) * (x - w)) (R : ℂ) z := by
    simpa using ((hasDerivAt_id z).sub_const w).const_mul (R : ℂ)
  have hd := hnum_d.div hden_d (mul_ne_zero hR' hzw')
  rw [logDeriv_apply]
  have hcf : canonicalFactor R w = (fun x : ℂ => (R : ℂ) ^ 2 - (starRingEnd ℂ) w * x) /
      fun x => (R : ℂ) * (x - w) := rfl
  rw [hcf, hd.deriv]
  simp only [Pi.div_apply]
  field_simp

/-- **Landau's lemma for the logarithmic derivative** (centre `0`, interior point `z`).

For `f` entire with `f 0 ≠ 0`, `‖f‖ ≤ M` on `closedBall 0 R`, no zeros on `sphere 0 R`, and a
point `z` with `‖z‖ ≤ R / 2` and `f z ≠ 0`,

  `‖f'(z)/f(z)‖ ≤ ∑_ρ m_ρ (1/‖z - ρ‖ + 2/R) + 24 (log M - log ‖f 0‖ + 1) / R`,

the sum over the zeros `ρ` of `f` in the open ball, with multiplicity `m_ρ`. -/
theorem norm_logDeriv_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {R M : ℝ}
    (hR : 0 < R) (hsph : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0) (hM : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ R / 2) (hfz : f z ≠ 0) :
    ‖logDeriv f z‖ ≤
      ∑ᶠ u, (((MeromorphicOn.divisor f (ball (0 : ℂ) R)) u).toNat : ℝ) * (1 / ‖z - u‖ + 2 / R)
        + 24 * (Real.log M - Real.log ‖f 0‖ + 1) / R := by
  have hon : AnalyticOnNhd ℂ f univ := fun x _ => hf.analyticAt x
  have hmer : MeromorphicOn f (closedBall (0 : ℂ) R) := fun x _ => (hf.analyticAt x).meromorphicAt
  have hord : ∀ u : closedBall (0 : ℂ) R, meromorphicOrderAt f u ≠ ⊤ := by
    intro u hu
    rw [(hf.analyticAt u).meromorphicOrderAt_eq] at hu
    have htop : analyticOrderAt f u = ⊤ := by
      by_contra hne
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
      rw [← hn] at hu
      simp at hu
    have hev : f =ᶠ[nhds (u : ℂ)] 0 := analyticOrderAt_eq_top.1 htop
    have hzero := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ (u : ℂ)) hev
    exact h0 (hzero (Set.mem_univ 0))
  obtain ⟨g, D⟩ := MeromorphicOn.exists_ecanonicalDecomp hmer hord
  have hsd : ∀ i, MeromorphicOn.divisor f (sphere (0 : ℂ) R) i = 0 := by
    intro i
    by_cases hi : i ∈ sphere (0 : ℂ) R
    · rw [MeromorphicOn.divisor_apply (hmer.mono_set sphere_subset_closedBall) hi]
      have hfi : f i ≠ 0 := hsph i (by simpa using hi)
      have : meromorphicOrderAt f i = 0 := by
        rw [(hf.analyticAt i).meromorphicOrderAt_eq,
          (hf.analyticAt i).analyticOrderAt_eq_zero.2 hfi]
        simp
      simp [this]
    · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hi
  have hord0 : ∀ w, f w ≠ 0 → meromorphicOrderAt f w = 0 := by
    intro w hw
    rw [(hf.analyticAt w).meromorphicOrderAt_eq, (hf.analyticAt w).analyticOrderAt_eq_zero.2 hw]
    simp
  -- the logarithm of the norm of `g`
  have hlog : ∀ w ∈ closedBall (0 : ℂ) R, f w ≠ 0 →
      Real.log ‖g w‖ = (∑ᶠ i, ((MeromorphicOn.divisor f (ball (0 : ℂ) R) i : ℤ) : ℝ) *
        Real.log ‖canonicalFactor R i w‖) + Real.log ‖f w‖ := by
    intro w hw hfw
    have := D.log_norm_eq hw (hord0 w hfw) hR
    simp only [hsd, Int.cast_zero, zero_mul, finsum_zero, sub_zero] at this
    rw [this, (hf.analyticAt w).meromorphicTrailingCoeffAt_of_ne_zero hfw]
  have hsupp : ∀ i, MeromorphicOn.divisor f (ball (0 : ℂ) R) i ≠ 0 → i ∈ ball (0 : ℂ) R :=
    fun i hi => (MeromorphicOn.divisor f (ball (0 : ℂ) R)).supportWithinDomain
      (Function.mem_support.2 hi)
  have hdn : ∀ i, 0 ≤ MeromorphicOn.divisor f (ball (0 : ℂ) R) i := fun i =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun x _ => hf.analyticAt x) i
  -- on the sphere, `‖g‖ = ‖f‖`
  have hgsph : ∀ w : ℂ, ‖w‖ = R → ‖g w‖ = ‖f w‖ := by
    intro w hw
    have hfw := hsph w hw
    have hgw : g w ≠ 0 := D.ne_zero w (by simp [hw])
    have h1 := hlog w (by simp [hw]) hfw
    have h2 : (∑ᶠ i, ((MeromorphicOn.divisor f (ball (0 : ℂ) R) i : ℤ) : ℝ) *
        Real.log ‖canonicalFactor R i w‖) = 0 := by
      refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
      by_cases hi : MeromorphicOn.divisor f (ball (0 : ℂ) R) i = 0
      · simp [hi]
      · rw [norm_canonicalFactor_eval_circle_eq_one (hsupp i hi) (by simpa using hw)]
        simp
    rw [h2, zero_add] at h1
    exact Real.log_injOn_pos (norm_pos_iff.2 hgw) (norm_pos_iff.2 hfw) h1
  -- `g` at the centre is at least as large as `f` at the centre
  have hg0 : Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ := by
    rw [hlog 0 (by simp [hR.le]) h0]
    have : 0 ≤ ∑ᶠ i, ((MeromorphicOn.divisor f (ball (0 : ℂ) R) i : ℤ) : ℝ) *
        Real.log ‖canonicalFactor R i 0‖ := by
      refine finsum_nonneg fun i => ?_
      by_cases hi : MeromorphicOn.divisor f (ball (0 : ℂ) R) i = 0
      · simp [hi]
      · have hib := hsupp i hi
        have hi0 : i ≠ 0 := by
          rintro rfl
          have : MeromorphicOn.divisor f (ball (0 : ℂ) R) 0 = 0 := by
            rw [MeromorphicOn.divisor_apply (fun x hx => hmer x (ball_subset_closedBall hx))
              (by simpa using hR)]
            simp [hord0 0 h0]
          exact hi this
        refine mul_nonneg (by exact_mod_cast hdn i) (Real.log_nonneg ?_)
        rw [canonicalFactor_apply]
        simp only [mul_zero, sub_zero, zero_sub, norm_div, norm_neg, norm_mul]
        have hn : ‖i‖ < R := by simpa using hib
        have hnpos : 0 < ‖i‖ := norm_pos_iff.2 hi0
        rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le,
          one_le_div (by positivity)]
        nlinarith
    linarith
  sorry

end Complex
