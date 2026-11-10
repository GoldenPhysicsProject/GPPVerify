/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import GppVerify.Upstream.LogDerivativeLandau
import GppVerify.Upstream.RectangleResidue

/-!
# The boundary integral of `(f'/f) Φ` over a rectangle is a sum over the zeros

For `f` entire with `f 0 ≠ 0` and `Φ` entire, and a rectangle with no zero of `f` on its boundary,
inside a ball `B(0, R)` whose sphere has no zero of `f`,

  `∮ (f'/f) Φ = 2 π i ∑_ρ m_ρ Φ(ρ)`,

summed over the zeros `ρ` strictly inside the rectangle, with multiplicity `m_ρ`. Mathlib has
Cauchy–Goursat for rectangles but no residue theorem; this derives the residue sum from the
Blaschke decomposition of `f'/f` on the ball (`Complex.exists_blaschke_decomposition`) and the
two basic computations `Complex.rectInt_div_sub` (a simple pole inside) and
`Complex.rectInt_div_sub_of_notMem` (a pole outside).
-/

open Complex Set Metric intervalIntegral
open scoped Interval

namespace Complex

theorem mem_rect_of_onRectBoundary {z w s : ℂ} (h : OnRectBoundary z w s) :
    s ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := by
  rw [Complex.mem_reProdIm]
  rcases h with ⟨hi, hr⟩ | ⟨hr, hi⟩
  · refine ⟨hr, ?_⟩
    rcases hi with hi | hi <;> rw [hi]
    · exact left_mem_uIcc
    · exact right_mem_uIcc
  · refine ⟨?_, hi⟩
    rcases hr with hr | hr <;> rw [hr]
    · exact left_mem_uIcc
    · exact right_mem_uIcc

theorem analyticOrderAt_ne_top_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (u : ℂ) : analyticOrderAt f u ≠ ⊤ := by
  intro htop
  have hev : f =ᶠ[nhds u] 0 := analyticOrderAt_eq_top.1 htop
  have hon : AnalyticOnNhd ℂ f Set.univ := fun x _ => hf.analyticAt x
  exact h0 ((hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ u) hev) (Set.mem_univ 0))

/-- A zero of an entire function that is not identically zero has nonzero divisor. -/
theorem divisor_ne_zero_of_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {U : Set ℂ}
    {ρ : ℂ} (hρU : ρ ∈ U) (hρ : f ρ = 0) : MeromorphicOn.divisor f U ρ ≠ 0 := by
  have hon : AnalyticOnNhd ℂ f U := fun x _ => hf.analyticAt x
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hon hρU]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_ne_top_of_entire hf h0 ρ)
  have hn0 : n ≠ 0 := by
    intro h
    have : analyticOrderAt f ρ = 0 := by rw [← hn, h]; rfl
    rw [(hf.analyticAt ρ).analyticOrderAt_eq_zero] at this
    exact this hρ
  rw [← hn]
  simpa using hn0

/-- **Residue sum for `(f'/f) Φ` over a rectangle.** -/
theorem rectInt_logDeriv_mul {f Φ : ℂ → ℂ} (hf : Differentiable ℂ f) (hΦ : Differentiable ℂ Φ)
    (h0 : f 0 ≠ 0) {R : ℝ} (hR : 0 < R) (hsph : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0) {z w : ℂ}
    (hzw : z.re < w.re ∧ z.im < w.im)
    (hsub : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ ball (0 : ℂ) R)
    (hbd : ∀ s, OnRectBoundary z w s → f s ≠ 0) :
    ∃ t : Finset ℂ, (∀ ρ ∈ t, ρ.re ∈ Ioo z.re w.re ∧ ρ.im ∈ Ioo z.im w.im ∧ f ρ = 0) ∧
      (∀ ρ : ℂ, ρ.re ∈ Ioo z.re w.re → ρ.im ∈ Ioo z.im w.im → f ρ = 0 → ρ ∈ t) ∧
      rectInt (fun s => logDeriv f s * Φ s) z w =
        2 * Real.pi * I * ∑ ρ ∈ t, ((MeromorphicOn.divisor f (ball (0 : ℂ) R) ρ : ℤ) : ℂ) * Φ ρ := by
  classical
  obtain ⟨g, t0, hgan, hgne, hgsph, hg0, htmem, htiff, hdn, hkey⟩ :=
    exists_blaschke_decomposition hf h0 hR hsph
  set D : ℂ → ℂ := fun i => ((MeromorphicOn.divisor f (ball (0 : ℂ) R) i : ℤ) : ℂ) with hD
  set T : Finset ℂ := t0.filter (fun ρ => ρ.re ∈ Ioo z.re w.re ∧ ρ.im ∈ Ioo z.im w.im) with hT
  have hrect : ∀ ρ : ℂ, ρ.re ∈ Ioo z.re w.re → ρ.im ∈ Ioo z.im w.im →
      ρ ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := by
    intro ρ h1 h2
    rw [Complex.mem_reProdIm, uIcc_of_le hzw.1.le, uIcc_of_le hzw.2.le]
    exact ⟨Ioo_subset_Icc_self h1, Ioo_subset_Icc_self h2⟩
  refine ⟨T, ?_, ?_, ?_⟩
  · intro ρ hρ
    rw [hT, Finset.mem_filter] at hρ
    exact ⟨hρ.2.1, hρ.2.2, (htmem ρ hρ.1).2⟩
  · intro ρ h1 h2 hfρ
    rw [hT, Finset.mem_filter, htiff]
    exact ⟨divisor_ne_zero_of_zero hf h0 (hsub (hrect ρ h1 h2)) hfρ, h1, h2⟩
  · -- the main identity
    have hcl : ∀ s, OnRectBoundary z w s → s ∈ ball (0 : ℂ) R := fun s hs =>
      hsub (mem_rect_of_onRectBoundary hs)
    -- pieces
    set A : ℂ → ℂ := fun s => logDeriv g s * Φ s with hA
    set B : ℂ → ℂ → ℂ := fun i s =>
      ((starRingEnd ℂ i) / ((R : ℂ) ^ 2 - (starRingEnd ℂ i) * s)) * Φ s with hB
    set C : ℂ → ℂ → ℂ := fun i s => Φ s / (s - i) with hC
    have hgd : ∀ s ∈ ball (0 : ℂ) R, AnalyticAt ℂ g s := fun s hs =>
      hgan s (ball_subset_closedBall hs)
    have hAd : ∀ s ∈ ball (0 : ℂ) R, DifferentiableAt ℂ A s := by
      intro s hs
      have h1 := (hgd s hs).deriv.differentiableAt
      have h2 := (hgd s hs).differentiableAt
      exact (h1.div h2 (hgne s (ball_subset_closedBall hs))).mul (hΦ s)
    have hden : ∀ i ∈ t0, ∀ s ∈ ball (0 : ℂ) R,
        (R : ℂ) ^ 2 - (starRingEnd ℂ i) * s ≠ 0 := by
      intro i hi s hs h
      have hib : ‖i‖ < R := by simpa using (htmem i hi).1
      have hsb : ‖s‖ < R := by simpa using hs
      have : ‖(starRingEnd ℂ i) * s‖ = ‖(R : ℂ) ^ 2‖ := by
        rw [sub_eq_zero] at h; rw [h]
      rw [norm_mul, Complex.norm_conj, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le] at this
      nlinarith [norm_nonneg i, norm_nonneg s]
    have hBd : ∀ i ∈ t0, ∀ s ∈ ball (0 : ℂ) R, DifferentiableAt ℂ (B i) s := by
      intro i hi s hs
      have : DifferentiableAt ℂ (fun s : ℂ => (R : ℂ) ^ 2 - (starRingEnd ℂ i) * s) s := by fun_prop
      exact ((differentiableAt_const _).div this (hden i hi s hs)).mul (hΦ s)
    have hfi : ∀ i ∈ t0, f i = 0 := fun i hi => (htmem i hi).2
    have hsi : ∀ i ∈ t0, ∀ s, OnRectBoundary z w s → s ≠ i := by
      intro i hi s hs h
      exact hbd s hs (h ▸ hfi i hi)
    have hCd : ∀ i ∈ t0, ∀ s, s ≠ i → DifferentiableAt ℂ (C i) s := by
      intro i hi s hsi
      exact (hΦ s).div (differentiableAt_id.sub_const i) (sub_ne_zero.mpr hsi)
    -- the boundary identity
    set G : ℂ → ℂ := fun s => A s + ∑ i ∈ t0, D i * (B i s + C i s) with hG
    have hFeq : ∀ s, OnRectBoundary z w s → logDeriv f s * Φ s = G s := by
      intro s hs
      have hsb := hcl s hs
      have hk := hkey s hsb (hbd s hs)
      have hterm : ∀ i ∈ t0, D i * logDeriv (canonicalFactor R i) s * Φ s =
          -(D i * (B i s + C i s)) := by
        intro i hi
        have hsi' := hsi i hi s hs
        have hcf := canonicalFactor_ne_zero (htmem i hi).1 (ball_subset_closedBall hsb) hsi'
        have hnum : (R : ℂ) ^ 2 - (starRingEnd ℂ i) * s ≠ 0 := by
          rw [canonicalFactor_apply] at hcf
          exact (div_ne_zero_iff.1 hcf).1
        rw [logDeriv_canonicalFactor hR.ne' hsi' hnum]
        have : s - i ≠ 0 := sub_ne_zero.mpr hsi'
        simp only [hB, hC]
        field_simp
        ring
      calc logDeriv f s * Φ s
          = (logDeriv g s - ∑ i ∈ t0, D i * logDeriv (canonicalFactor R i) s) * Φ s := by
            rw [hk]
        _ = A s - ∑ i ∈ t0, D i * logDeriv (canonicalFactor R i) s * Φ s := by
            rw [sub_mul, Finset.sum_mul]
        _ = G s := by
            rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
            simp only [hG]
            ring
    rw [rectInt_congr hFeq]
    -- edge integrability
    have hAe : EdgeInt A z w := edgeInt_of_continuousAt_boundary fun s hs =>
      (hAd s (hcl s hs)).continuousAt
    have hBe : ∀ i ∈ t0, EdgeInt (B i) z w := fun i hi =>
      edgeInt_of_continuousAt_boundary fun s hs => (hBd i hi s (hcl s hs)).continuousAt
    have hCe : ∀ i ∈ t0, EdgeInt (C i) z w := fun i hi =>
      edgeInt_of_continuousAt_boundary fun s hs => (hCd i hi s (hsi i hi s hs)).continuousAt
    have hTe : ∀ i ∈ t0, EdgeInt (fun s => D i * (B i s + C i s)) z w := fun i hi =>
      ((hBe i hi).add (hCe i hi)).const_mul (D i)
    have hGsplit : rectInt G z w = rectInt A z w +
        ∑ i ∈ t0, D i * (rectInt (B i) z w + rectInt (C i) z w) := by
      rw [hG, rectInt_add hAe (EdgeInt.finset_sum t0 hTe), rectInt_finset_sum t0 hTe]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [rectInt_const_mul, rectInt_add (hBe i hi) (hCe i hi)]
    have hA0 : rectInt A z w = 0 :=
      rectInt_eq_zero_of_differentiableOn z w fun s hs =>
        (hAd s (hsub hs)).differentiableWithinAt
    have hB0 : ∀ i ∈ t0, rectInt (B i) z w = 0 := fun i hi =>
      rectInt_eq_zero_of_differentiableOn z w fun s hs =>
        (hBd i hi s (hsub hs)).differentiableWithinAt
    have hCval : ∀ i ∈ t0, rectInt (C i) z w =
        if (i.re ∈ Ioo z.re w.re ∧ i.im ∈ Ioo z.im w.im) then 2 * Real.pi * I * Φ i else 0 := by
      intro i hi
      by_cases hin : i.re ∈ Ioo z.re w.re ∧ i.im ∈ Ioo z.im w.im
      · rw [if_pos hin]
        exact rectInt_div_sub hΦ hin.1.1 hin.1.2 hin.2.1 hin.2.2
      · rw [if_neg hin]
        refine rectInt_div_sub_of_notMem hΦ fun hmem => ?_
        rw [Complex.mem_reProdIm, uIcc_of_le hzw.1.le, uIcc_of_le hzw.2.le] at hmem
        refine hbd i ?_ (hfi i hi)
        obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := hmem
        have hre : i.re ∈ uIcc z.re w.re := by rw [uIcc_of_le hzw.1.le]; exact ⟨hr1, hr2⟩
        have him : i.im ∈ uIcc z.im w.im := by rw [uIcc_of_le hzw.2.le]; exact ⟨hi1, hi2⟩
        rcases hr1.eq_or_lt with hr | hr
        · exact Or.inr ⟨Or.inl hr.symm, him⟩
        rcases hr2.eq_or_lt with hr' | hr'
        · exact Or.inr ⟨Or.inr hr', him⟩
        rcases hi1.eq_or_lt with hj | hj
        · exact Or.inl ⟨Or.inl hj.symm, hre⟩
        rcases hi2.eq_or_lt with hj' | hj'
        · exact Or.inl ⟨Or.inr hj', hre⟩
        exact absurd ⟨⟨hr, hr'⟩, ⟨hj, hj'⟩⟩ hin
    rw [hGsplit, hA0, zero_add]
    have h1 : ∑ i ∈ t0, D i * (rectInt (B i) z w + rectInt (C i) z w) =
        ∑ i ∈ t0, (if (i.re ∈ Ioo z.re w.re ∧ i.im ∈ Ioo z.im w.im) then
          2 * Real.pi * I * (D i * Φ i) else 0) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hB0 i hi, hCval i hi, zero_add]
      split_ifs <;> ring
    rw [h1, ← Finset.sum_filter, ← Finset.mul_sum]

end Complex
