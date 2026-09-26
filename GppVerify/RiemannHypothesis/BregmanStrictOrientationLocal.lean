import GppVerify.RiemannHypothesis.BregmanTriangularKernel
import GppVerify.RiemannHypothesis.KLOrientationKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Local strict orientation of one-parameter Gibbs Bregman divergences

This version uses only continuity of the Fisher metric on the compact parameter
interval.  That is the natural hypothesis for the zeta Gibbs family on `β>1` and
avoids any artificial global extension of the Fisher metric.
-/

namespace GppBregmanStrictOrientationLocal

open Set MeasureTheory intervalIntegral
open GppZetaGibbsInformationGeometry
open GppBregmanTriangularKernel
open GppKLOrientationKernel

/-- Local midpoint reflection identity under continuity only on `[β,γ]`. -/
theorem antisymmetric_integral_eq_reflected_local
    (g : ℝ → ℝ) {β γ : ℝ} (hβγ : β ≤ γ)
    (hg : ContinuousOn g (Icc β γ)) :
    (∫ x in β..γ, (β + γ - 2 * x) * g x) =
      ∫ y in (0 : ℝ)..((γ - β) / 2),
        reflectedKernel g ((β + γ) / 2) y := by
  let m : ℝ := (β + γ) / 2
  let L : ℝ := (γ - β) / 2
  let f : ℝ → ℝ := fun x => (β + γ - 2 * x) * g x
  have hβm : β ≤ m := by dsimp [m]; linarith
  have hmγ : m ≤ γ := by dsimp [m]; linarith
  have hfcont : ContinuousOn f (Icc β γ) := by
    dsimp [f]
    exact (by fun_prop : Continuous (fun x : ℝ => β + γ - 2 * x)).continuousOn.mul hg
  have hfβm : ContinuousOn f (Icc β m) := hfcont.mono (by
    intro x hx
    exact ⟨hx.1, hx.2.trans hmγ⟩)
  have hfmγ : ContinuousOn f (Icc m γ) := hfcont.mono (by
    intro x hx
    exact ⟨hβm.trans hx.1, hx.2⟩)
  have hiβm : IntervalIntegrable f volume β m := by
    have hc : ContinuousOn f [[β, m]] := by simpa [uIcc_of_le hβm] using hfβm
    exact hc.intervalIntegrable
  have himγ : IntervalIntegrable f volume m γ := by
    have hc : ContinuousOn f [[m, γ]] := by simpa [uIcc_of_le hmγ] using hfmγ
    exact hc.intervalIntegrable
  have hsplit :
      (∫ x in β..γ, f x) = (∫ x in β..m, f x) + ∫ x in m..γ, f x := by
    exact (intervalIntegral.integral_add_adjacent_intervals hiβm himγ).symm
  have hleft :
      (∫ x in β..m, f x) = ∫ y in (0 : ℝ)..L, f (m - y) := by
    have h := intervalIntegral.integral_comp_sub_left (f := f) (a := (0 : ℝ)) (b := L) m
    rw [show m - L = β by dsimp [m, L]; ring,
        show m - 0 = m by ring] at h
    exact h.symm
  have hright :
      (∫ x in m..γ, f x) = ∫ y in (0 : ℝ)..L, f (y + m) := by
    have h := intervalIntegral.integral_comp_add_right (f := f) (a := (0 : ℝ)) (b := L) m
    rw [show 0 + m = m by ring,
        show L + m = γ by dsimp [m, L]; ring] at h
    exact h.symm
  rw [show (∫ x in β..γ, (β + γ - 2 * x) * g x) = ∫ x in β..γ, f x by rfl]
  rw [hsplit, hleft, hright, ← intervalIntegral.integral_add]
  apply intervalIntegral.integral_congr
  intro y hy
  dsimp [f, m, reflectedKernel]
  ring

/-- Local continuity makes the reflected kernel interval-integrable. -/
theorem reflectedKernel_intervalIntegrable_local
    (g : ℝ → ℝ) {m L : ℝ} (hL : 0 ≤ L)
    (hg : ContinuousOn g (Icc (m - L) (m + L))) :
    IntervalIntegrable (reflectedKernel g m) volume 0 L := by
  have hleftMap : MapsTo (fun y : ℝ => m - y) (Icc 0 L) (Icc (m - L) (m + L)) := by
    intro y hy
    constructor <;> linarith [hy.1, hy.2]
  have hrightMap : MapsTo (fun y : ℝ => m + y) (Icc 0 L) (Icc (m - L) (m + L)) := by
    intro y hy
    constructor <;> linarith [hy.1, hy.2]
  have hleft : ContinuousOn (fun y : ℝ => g (m - y)) (Icc 0 L) :=
    hg.comp (by fun_prop) hleftMap
  have hright : ContinuousOn (fun y : ℝ => g (m + y)) (Icc 0 L) :=
    hg.comp (by fun_prop) hrightMap
  have hk : ContinuousOn (reflectedKernel g m) (Icc 0 L) := by
    unfold reflectedKernel
    exact (by fun_prop : Continuous (fun y : ℝ => 2 * y)).continuousOn.mul (hleft.sub hright)
  have hku : ContinuousOn (reflectedKernel g m) [[(0 : ℝ), L]] := by
    simpa [uIcc_of_le hL] using hk
  exact hku.intervalIntegrable

/-- Strict positivity of the local reflected kernel integral. -/
theorem reflectedKernel_integral_pos_local
    (g : ℝ → ℝ) {m L : ℝ} (hL : 0 < L)
    (hgcont : ContinuousOn g (Icc (m - L) (m + L)))
    (hganti : ∀ y ∈ Ioo (0 : ℝ) L, g (m + y) < g (m - y)) :
    0 < ∫ y in (0 : ℝ)..L, reflectedKernel g m y := by
  apply intervalIntegral_pos_of_pos_on
    (reflectedKernel_intervalIntegrable_local g hL.le hgcont)
  · intro y hy
    exact reflectedKernel_pos hy.1 (hganti y hy)
  · exact hL

/-- **Strict Bregman/KL orientation from local Fisher decrease.** -/
theorem bregmanKL_gt_reverse_of_fisher_strictAnti_local
    (A U g : ℝ → ℝ) {β γ : ℝ}
    (hβγ : β < γ)
    (hA : ∀ x ∈ [[β, γ]], HasDerivAt A (-U x) x)
    (hU : ∀ x ∈ [[β, γ]], HasDerivAt U (-g x) x)
    (hgcont : ContinuousOn g (Icc β γ))
    (hganti : ∀ ⦃x y : ℝ⦄, β ≤ x → y ≤ γ → x < y → g y < g x) :
    bregmanKL A U γ β < bregmanKL A U β γ := by
  have hcontU : ContinuousOn g [[β, γ]] := by
    simpa [uIcc_of_le hβγ.le] using hgcont
  rw [bregmanKL_eq_triangular A U g β γ hA hU hcontU]
  rw [bregmanKL_reverse_eq_triangular A U g β γ hA hU hcontU]
  have hsub :
      (∫ x in β..γ, (γ - x) * g x) -
          (∫ x in β..γ, (x - β) * g x) =
        ∫ x in β..γ, (β + γ - 2 * x) * g x := by
    rw [← intervalIntegral.integral_sub]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [lt_iff_sub_pos, hsub,
    antisymmetric_integral_eq_reflected_local g hβγ.le hgcont]
  let m : ℝ := (β + γ) / 2
  let L : ℝ := (γ - β) / 2
  have hL : 0 < L := by dsimp [L]; linarith
  have hbounds : Icc (m - L) (m + L) = Icc β γ := by
    dsimp [m, L]
    congr 1 <;> ring
  apply reflectedKernel_integral_pos_local g hL
  · simpa [hbounds] using hgcont
  · intro y hy
    have hxlo : β ≤ m - y := by dsimp [m, L] at hy ⊢; linarith
    have hyhi : m + y ≤ γ := by dsimp [m, L] at hy ⊢; linarith
    have hxy : m - y < m + y := by linarith [hy.1]
    exact hganti hxlo hyhi hxy

end GppBregmanStrictOrientationLocal

#print axioms GppBregmanStrictOrientationLocal.bregmanKL_gt_reverse_of_fisher_strictAnti_local
