/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import GppVerify.Upstream.RectangleWinding
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Boundary integrals over a rectangle: linearity and residues of simple poles

`Complex.rectInt F z w` is the boundary integral of `F` over the rectangle with corners `z` and
`w`, in exactly the form used by `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.
It is additive and homogeneous in `F` as long as the four edge integrands are interval
integrable, depends only on the values of `F` on the boundary, vanishes for `F` holomorphic on the
closed rectangle, and equals `2 π i * Φ ρ` for `F s = Φ s / (s - ρ)` with `Φ` entire and `ρ`
strictly inside.
-/

open Complex Set intervalIntegral
open scoped Interval

namespace Complex

/-- The boundary integral of `F` over the rectangle with corners `z` and `w`. -/
noncomputable def rectInt (F : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
    I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))

/-- The four edge integrands of `F` are interval integrable. -/
def EdgeInt (F : ℂ → ℂ) (z w : ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => F (x + z.im * I)) MeasureTheory.volume z.re w.re ∧
  IntervalIntegrable (fun x : ℝ => F (x + w.im * I)) MeasureTheory.volume z.re w.re ∧
  IntervalIntegrable (fun y : ℝ => F (w.re + y * I)) MeasureTheory.volume z.im w.im ∧
  IntervalIntegrable (fun y : ℝ => F (z.re + y * I)) MeasureTheory.volume z.im w.im

/-- `s` lies on the boundary of the rectangle with corners `z`, `w`. -/
def OnRectBoundary (z w s : ℂ) : Prop :=
  ((s.im = z.im ∨ s.im = w.im) ∧ s.re ∈ uIcc z.re w.re) ∨
  ((s.re = z.re ∨ s.re = w.re) ∧ s.im ∈ uIcc z.im w.im)

theorem rectInt_eq_zero_of_differentiableOn {F : ℂ → ℂ} (z w : ℂ)
    (H : DifferentiableOn ℂ F ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) : rectInt F z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn F z w H

theorem rectInt_congr {F G : ℂ → ℂ} {z w : ℂ}
    (h : ∀ s, OnRectBoundary z w s → F s = G s) : rectInt F z w = rectInt G z w := by
  unfold rectInt
  have e1 : ∫ x : ℝ in z.re..w.re, F (x + z.im * I) = ∫ x : ℝ in z.re..w.re, G (x + z.im * I) :=
    integral_congr fun x hx => h _ (Or.inl ⟨Or.inl (by simp), by simpa using hx⟩)
  have e2 : ∫ x : ℝ in z.re..w.re, F (x + w.im * I) = ∫ x : ℝ in z.re..w.re, G (x + w.im * I) :=
    integral_congr fun x hx => h _ (Or.inl ⟨Or.inr (by simp), by simpa using hx⟩)
  have e3 : ∫ y : ℝ in z.im..w.im, F (w.re + y * I) = ∫ y : ℝ in z.im..w.im, G (w.re + y * I) :=
    integral_congr fun y hy => h _ (Or.inr ⟨Or.inr (by simp), by simpa using hy⟩)
  have e4 : ∫ y : ℝ in z.im..w.im, F (z.re + y * I) = ∫ y : ℝ in z.im..w.im, G (z.re + y * I) :=
    integral_congr fun y hy => h _ (Or.inr ⟨Or.inl (by simp), by simpa using hy⟩)
  rw [e1, e2, e3, e4]

theorem rectInt_add {F G : ℂ → ℂ} {z w : ℂ} (hF : EdgeInt F z w) (hG : EdgeInt G z w) :
    rectInt (fun s => F s + G s) z w = rectInt F z w + rectInt G z w := by
  obtain ⟨a1, a2, a3, a4⟩ := hF
  obtain ⟨b1, b2, b3, b4⟩ := hG
  unfold rectInt
  simp only [integral_add a1 b1, integral_add a2 b2, integral_add a3 b3, integral_add a4 b4,
    smul_eq_mul, mul_add]
  ring

theorem rectInt_const_mul {F : ℂ → ℂ} {z w : ℂ} (c : ℂ) :
    rectInt (fun s => c * F s) z w = c * rectInt F z w := by
  unfold rectInt
  simp only [integral_const_mul, smul_eq_mul]
  ring

/-- The edge integrands of `(s - ρ)⁻¹` are interval integrable when no edge passes through `ρ`. -/
theorem edgeInt_inv_sub {z w ρ : ℂ} (hzr : z.re ≠ ρ.re) (hwr : w.re ≠ ρ.re)
    (hzi : z.im ≠ ρ.im) (hwi : w.im ≠ ρ.im) : EdgeInt (fun s => (s - ρ)⁻¹) z w := by
  have hh : ∀ y : ℝ, y ≠ ρ.im → Continuous (fun x : ℝ => (((x : ℂ) + y * I) - ρ)⁻¹) := by
    intro y hy
    refine Continuous.inv₀ (by fun_prop) fun x h => hy ?_
    have := congrArg Complex.im h
    simp at this
    linarith
  have hv : ∀ x : ℝ, x ≠ ρ.re → Continuous (fun y : ℝ => (((x : ℂ) + y * I) - ρ)⁻¹) := by
    intro x hx
    refine Continuous.inv₀ (by fun_prop) fun y h => hx ?_
    have := congrArg Complex.re h
    simp at this
    linarith
  exact ⟨(hh _ hzi).intervalIntegrable _ _, (hh _ hwi).intervalIntegrable _ _,
    (hv _ hwr).intervalIntegrable _ _, (hv _ hzr).intervalIntegrable _ _⟩

theorem EdgeInt.const_mul {F : ℂ → ℂ} {z w : ℂ} (h : EdgeInt F z w) (c : ℂ) :
    EdgeInt (fun s => c * F s) z w :=
  ⟨h.1.const_mul c, h.2.1.const_mul c, h.2.2.1.const_mul c, h.2.2.2.const_mul c⟩

theorem edgeInt_of_continuous {F : ℂ → ℂ} (hF : Continuous F) (z w : ℂ) : EdgeInt F z w :=
  ⟨(hF.comp (by fun_prop)).intervalIntegrable _ _, (hF.comp (by fun_prop)).intervalIntegrable _ _,
    (hF.comp (by fun_prop)).intervalIntegrable _ _, (hF.comp (by fun_prop)).intervalIntegrable _ _⟩

/-- **A simple pole inside the rectangle.** For `Φ` entire and `ρ` strictly inside the rectangle
with corners `z`, `w`, the boundary integral of `Φ s / (s - ρ)` is `2 π i Φ ρ`. -/
theorem rectInt_div_sub {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {z w ρ : ℂ} (hzr : z.re < ρ.re)
    (hrw : ρ.re < w.re) (hzi : z.im < ρ.im) (hiw : ρ.im < w.im) :
    rectInt (fun s => Φ s / (s - ρ)) z w = 2 * Real.pi * I * Φ ρ := by
  have hdd : Differentiable ℂ (dslope Φ ρ) := fun x =>
    ((differentiableOn_dslope (Filter.univ_mem)).2 hΦ.differentiableOn x (Set.mem_univ _)).differentiableAt
      Filter.univ_mem
  have hedge := edgeInt_inv_sub hzr.ne hrw.ne' hzi.ne hiw.ne'
  have hcongr : rectInt (fun s => Φ s / (s - ρ)) z w =
      rectInt (fun s => dslope Φ ρ s + Φ ρ * (s - ρ)⁻¹) z w := by
    refine rectInt_congr fun s hs => ?_
    have hsρ : s ≠ ρ := by
      intro h
      subst h
      rcases hs with ⟨hi, -⟩ | ⟨hr, -⟩
      · rcases hi with hi | hi <;> linarith
      · rcases hr with hr | hr <;> linarith
    rw [dslope_of_ne _ hsρ, slope_def_field]
    have : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ
    field_simp
    ring
  rw [hcongr, rectInt_add (edgeInt_of_continuous hdd.continuous z w)
    (hedge.const_mul (Φ ρ)),
    rectInt_eq_zero_of_differentiableOn z w hdd.differentiableOn, rectInt_const_mul]
  have := rect_boundary_integral_inv_sub hzr hrw hzi hiw
  have h2 : rectInt (fun s => (s - ρ)⁻¹) z w = 2 * Real.pi * I := this
  rw [h2]
  ring

/-- The edge integrands are interval integrable when `F` is continuous at every boundary point. -/
theorem edgeInt_of_continuousAt_boundary {F : ℂ → ℂ} {z w : ℂ}
    (h : ∀ s, OnRectBoundary z w s → ContinuousAt F s) : EdgeInt F z w := by
  have hc1 : ContinuousOn (fun x : ℝ => F (x + z.im * I)) (uIcc z.re w.re) := fun x hx =>
    ((h _ (Or.inl ⟨Or.inl (by simp), by simpa using hx⟩)).comp
      (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + z.im * I).continuousAt).continuousWithinAt
  have hc2 : ContinuousOn (fun x : ℝ => F (x + w.im * I)) (uIcc z.re w.re) := fun x hx =>
    ((h _ (Or.inl ⟨Or.inr (by simp), by simpa using hx⟩)).comp
      (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + w.im * I).continuousAt).continuousWithinAt
  have hc3 : ContinuousOn (fun y : ℝ => F (w.re + y * I)) (uIcc z.im w.im) := fun y hy =>
    ((h _ (Or.inr ⟨Or.inr (by simp), by simpa using hy⟩)).comp
      (by fun_prop : Continuous fun y : ℝ => (w.re : ℂ) + y * I).continuousAt).continuousWithinAt
  have hc4 : ContinuousOn (fun y : ℝ => F (z.re + y * I)) (uIcc z.im w.im) := fun y hy =>
    ((h _ (Or.inr ⟨Or.inl (by simp), by simpa using hy⟩)).comp
      (by fun_prop : Continuous fun y : ℝ => (z.re : ℂ) + y * I).continuousAt).continuousWithinAt
  exact ⟨hc1.intervalIntegrable, hc2.intervalIntegrable, hc3.intervalIntegrable,
    hc4.intervalIntegrable⟩

/-- **A pole outside the closed rectangle contributes nothing.** -/
theorem rectInt_div_sub_of_notMem {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {z w ρ : ℂ}
    (hρ : ρ ∉ [[z.re, w.re]] ×ℂ [[z.im, w.im]]) :
    rectInt (fun s => Φ s / (s - ρ)) z w = 0 := by
  refine rectInt_eq_zero_of_differentiableOn z w fun s hs => ?_
  have hne : s - ρ ≠ 0 := sub_ne_zero.mpr fun h => hρ (h ▸ hs)
  exact ((hΦ s).div (differentiableAt_id.sub_const ρ) hne).differentiableWithinAt

end Complex
