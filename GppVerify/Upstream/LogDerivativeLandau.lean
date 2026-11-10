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

/-- **Blaschke decomposition of the logarithmic derivative** (centre `0`).

For `f` entire with `f 0 ≠ 0` and no zeros on `sphere 0 R` there are a zero-free analytic `g` on the
closed ball (with `‖g‖ = ‖f‖` on the sphere and `‖g 0‖ ≥ ‖f 0‖`) and the finite set `t` of zeros in the
open ball such that, for `z` in the open ball with `f z ≠ 0`,

  `f'/f (z) = g'/g (z) - ∑_{ρ ∈ t} m_ρ (canonical factor)'/(canonical factor) (z)`,

with `m_ρ` the divisor of `f` on the ball, i.e. the multiplicity. -/
theorem exists_blaschke_decomposition {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    {R : ℝ} (hR : 0 < R) (hsph : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0) :
    ∃ (g : ℂ → ℂ) (t : Finset ℂ), AnalyticOnNhd ℂ g (closedBall (0 : ℂ) R) ∧
      (∀ w ∈ closedBall (0 : ℂ) R, g w ≠ 0) ∧ (∀ w : ℂ, ‖w‖ = R → ‖g w‖ = ‖f w‖) ∧
      Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ ∧
      (∀ i ∈ t, i ∈ ball (0 : ℂ) R ∧ f i = 0) ∧
      (∀ i, i ∈ t ↔ MeromorphicOn.divisor f (ball (0 : ℂ) R) i ≠ 0) ∧
      (∀ i, 0 ≤ MeromorphicOn.divisor f (ball (0 : ℂ) R) i) ∧
      (∀ z ∈ ball (0 : ℂ) R, f z ≠ 0 →
        logDeriv f z = logDeriv g z -
          ∑ i ∈ t, ((MeromorphicOn.divisor f (ball (0 : ℂ) R) i : ℤ) : ℂ) *
            logDeriv (canonicalFactor R i) z) := by
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
  have hgan : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) R) := D.analyticOnNhd
  have hfin := hmer.divisor_ball_support_finite
  set t := hfin.toFinset with ht
  set Dv : ℂ → ℤ := fun i => MeromorphicOn.divisor f (ball (0 : ℂ) R) i with hDv
  have hball : ∀ i ∈ t, i ∈ ball (0 : ℂ) R := fun i hi =>
    hsupp i (by simpa [ht] using hi)
  have hzeros : ∀ i ∈ t, f i = 0 := by
    intro i hi
    by_contra hfi
    have hi' : Dv i ≠ 0 := by simpa [ht] using hi
    apply hi'
    simp only [hDv]
    rw [MeromorphicOn.divisor_apply (fun x hx => hmer x (ball_subset_closedBall hx)) (hball i hi),
      hord0 i hfi]
    simp
  refine ⟨g, t, hgan, fun w hw => D.ne_zero w hw, hgsph, hg0,
    fun i hi => ⟨hball i hi, hzeros i hi⟩, fun i => by simp [ht], hdn, ?_⟩
  intro z hzb hfz
  have hzi : ∀ i ∈ t, z ≠ i := fun i hi h => hfz (h ▸ hzeros i hi)
  have hzc : z ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hzb
  have hcz : ∀ i ∈ t, canonicalFactor R i z ≠ 0 := fun i hi =>
    canonicalFactor_ne_zero (hball i hi) hzc (hzi i hi)
  have hcd : ∀ i ∈ t, DifferentiableAt ℂ (fun w => canonicalFactor R i w ^ Dv i) z := by
    intro i hi
    have h1 : DifferentiableAt ℂ (canonicalFactor R i) z :=
      (analyticOnNhd_canonicalFactor R i z (by simpa using hzi i hi)).differentiableAt
    exact h1.zpow (Or.inl (hcz i hi))
  set P : ℂ → ℂ := fun w => ∏ i ∈ t, canonicalFactor R i w ^ Dv i with hP
  have hgP : g =ᶠ[nhds z] fun w => P w * f w := by
    filter_upwards [isOpen_ball.mem_nhds hzb, hf.continuous.continuousAt.eventually_ne hfz]
      with w hw hfw
    have := D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
      (ball_subset_closedBall hw) (hord0 w hfw) hR
    simp only [Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply, hsd, neg_zero, zpow_zero,
      finprod_one, mul_one, smul_eq_mul] at this
    rw [this, (hf.analyticAt w).meromorphicTrailingCoeffAt_of_ne_zero hfw]
    congr 1
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro i hi
    rw [Function.mem_mulSupport] at hi
    have : Dv i ≠ 0 := fun h0' => hi (by
      have h00 : (MeromorphicOn.divisor f (ball (0 : ℂ) R)) i = 0 := h0'
      rw [h00, zpow_zero])
    simpa [ht] using this
  have hPz : P z ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => zpow_ne_zero _ (hcz i hi)
  have hPd : DifferentiableAt ℂ P z := DifferentiableAt.fun_finsetProd hcd
  have hcdiff : ∀ i ∈ t, DifferentiableAt ℂ (canonicalFactor R i) z := fun i hi =>
    (analyticOnNhd_canonicalFactor R i z (by simpa using hzi i hi)).differentiableAt
  have hlogP : logDeriv P z = ∑ i ∈ t, (Dv i : ℂ) * logDeriv (canonicalFactor R i) z := by
    rw [hP, logDeriv_prod (f := fun i w => canonicalFactor R i w ^ Dv i) (s := t)
      (fun i hi => zpow_ne_zero _ (hcz i hi)) hcd]
    exact Finset.sum_congr rfl fun i hi => logDeriv_fun_zpow (hcdiff i hi) (Dv i)
  have hsplit : logDeriv g z = logDeriv P z + logDeriv f z := by
    have : logDeriv g z = logDeriv (fun w => P w * f w) z := by
      rw [logDeriv_apply, logDeriv_apply, hgP.deriv_eq, hgP.eq_of_nhds]
    rw [this, logDeriv_mul z hPz hfz hPd (hf.differentiableAt)]
  have key : logDeriv f z = logDeriv g z - ∑ i ∈ t, (Dv i : ℂ) * logDeriv (canonicalFactor R i) z := by
    rw [hsplit, hlogP]; ring
  exact key

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
  obtain ⟨g, t, hgan, hgne', hgsph, hg0, htmem, htiff, hdn, hkey⟩ :=
    exists_blaschke_decomposition hf h0 hR hsph
  -- maximum principle: `‖g‖ ≤ M` on the closed ball
  have hgM : ∀ w : ℂ, ‖w‖ ≤ R → ‖g w‖ ≤ M := by
    intro w hw
    have hd : DiffContOnCl ℂ g (ball (0 : ℂ) R) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball _ hR.ne']
      exact fun x hx => (hgan x hx).differentiableAt.differentiableWithinAt
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball) hd ?_
      (by rw [closure_ball _ hR.ne']; simpa using hw)
    intro x hx
    rw [frontier_ball _ hR.ne'] at hx
    have hx' : ‖x‖ = R := by simpa using hx
    rw [hgsph x hx']
    exact hM x hx'.le
  -- a holomorphic logarithm of `g`
  have hgne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0 := fun w hw => hgne' w (ball_subset_closedBall hw)
  obtain ⟨h, hhd, hgh⟩ := exists_exp_eq_of_ne_zero_ball
    (fun x hx => (hgan x (ball_subset_closedBall hx)).differentiableAt.differentiableWithinAt) hgne
  have hM0 : ‖f 0‖ ≤ M := hM 0 (by simp [hR.le])
  have hf0pos : 0 < ‖f 0‖ := norm_pos_iff.2 h0
  have hM1 : 0 < Real.log M - Real.log ‖f 0‖ + 1 := by
    have := Real.log_le_log hf0pos hM0
    linarith
  have hre : ∀ w ∈ ball (0 : ℂ) R,
      (h w - h 0).re ≤ Real.log M - Real.log ‖f 0‖ + 1 := by
    intro w hw
    have e : ∀ x ∈ ball (0 : ℂ) R, (h x).re = Real.log ‖g x‖ := by
      intro x hx
      rw [hgh x hx, Complex.norm_exp, Real.log_exp]
    rw [sub_re, e w hw, e 0 (mem_ball_self hR)]
    have : Real.log ‖g w‖ ≤ Real.log M :=
      Real.log_le_log (norm_pos_iff.2 (hgne w hw)) (hgM w (mem_ball_zero_iff.1 hw).le)
    linarith
  have hzb : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; linarith
  have hdh : ‖deriv h z‖ ≤ 24 * (Real.log M - Real.log ‖f 0‖ + 1) / R :=
    norm_deriv_le_of_re_le hM1 hR hhd hre (by simpa using hz)
  -- `logDeriv g = h'`
  have hlogg : logDeriv g z = deriv h z := by
    have hev : g =ᶠ[nhds z] fun w => exp (h w) := by
      filter_upwards [isOpen_ball.mem_nhds hzb] with w hw using hgh w hw
    have hhz : DifferentiableAt ℂ h z := (hhd z hzb).differentiableAt (isOpen_ball.mem_nhds hzb)
    rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    rw [deriv_cexp hhz]
    have := exp_ne_zero (h z)
    field_simp
  set Dv : ℂ → ℤ := fun i => MeromorphicOn.divisor f (ball (0 : ℂ) R) i with hDv
  have hzi : ∀ i ∈ t, z ≠ i := fun i hi h => hfz (h ▸ (htmem i hi).2)
  have hzc : z ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hzb
  have hcz : ∀ i ∈ t, canonicalFactor R i z ≠ 0 := fun i hi =>
    canonicalFactor_ne_zero (htmem i hi).1 hzc (hzi i hi)
  have hball : ∀ i ∈ t, i ∈ ball (0 : ℂ) R := fun i hi => (htmem i hi).1
  have key := hkey z hzb hfz
  -- termwise bound
  have hterm : ∀ i ∈ t, ‖(Dv i : ℂ) * logDeriv (canonicalFactor R i) z‖ ≤
      ((Dv i).toNat : ℝ) * (1 / ‖z - i‖ + 2 / R) := by
    intro i hi
    have hib : ‖i‖ < R := by simpa using hball i hi
    have hnum : (R : ℂ) ^ 2 - (starRingEnd ℂ) i * z ≠ 0 := by
      have := hcz i hi
      rw [canonicalFactor_apply] at this
      exact (div_ne_zero_iff.1 this).1
    have hlc := logDeriv_canonicalFactor hR.ne' (hzi i hi) hnum
    have hDnat : (Dv i : ℂ) = ((Dv i).toNat : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg (hdn i)).symm
    rw [norm_mul, hDnat, Complex.norm_natCast, hlc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine (norm_sub_le _ _).trans ?_
    have hzi' : 0 < ‖z - i‖ := norm_pos_iff.2 (sub_ne_zero.2 (hzi i hi))
    have h1 : ‖(1 : ℂ) / (z - i)‖ = 1 / ‖z - i‖ := by simp
    have h2 : ‖-(starRingEnd ℂ) i / ((R : ℂ) ^ 2 - (starRingEnd ℂ) i * z)‖ ≤ 2 / R := by
      have hden : R ^ 2 / 2 ≤ ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) i * z‖ := by
        have h3 : ‖(R : ℂ) ^ 2‖ - ‖(starRingEnd ℂ) i * z‖ ≤
            ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) i * z‖ := norm_sub_norm_le _ _
        have h4 : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
          rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le]
        have h5 : ‖(starRingEnd ℂ) i * z‖ ≤ R * (R / 2) := by
          rw [norm_mul, Complex.norm_conj]
          exact mul_le_mul hib.le hz (norm_nonneg _) hR.le
        nlinarith
      rw [norm_div, norm_neg, Complex.norm_conj]
      rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hden) hR]
      nlinarith [norm_nonneg i]
    linarith
  -- assemble
  rw [key]
  refine (norm_sub_le _ _).trans ?_
  rw [hlogg]
  have hsum : ‖∑ i ∈ t, (Dv i : ℂ) * logDeriv (canonicalFactor R i) z‖ ≤
      ∑ᶠ u, (((MeromorphicOn.divisor f (ball (0 : ℂ) R)) u).toNat : ℝ) * (1 / ‖z - u‖ + 2 / R) := by
    refine (norm_sum_le _ _).trans ?_
    rw [finsum_eq_sum_of_support_subset (s := t)]
    · exact Finset.sum_le_sum hterm
    · intro u hu
      rw [Function.mem_support] at hu
      have : Dv u ≠ 0 := fun h0' => hu (by
        have h00 : (MeromorphicOn.divisor f (ball (0 : ℂ) R)) u = 0 := h0'
        simp [h00])
      exact (htiff u).2 this
  linarith

end Complex
