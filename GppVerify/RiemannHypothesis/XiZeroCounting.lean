/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Divisor
import GppVerify.RiemannHypothesis.LogDerivativeZeroFree

/-!
# Explicit formula, stage E3b (part 1): multiplicities of `ξ` and `ζ` agree in the strip

For `0 < Re ρ < 1` the orders of vanishing of `ξ` and `ζ` at `ρ` coincide, because
`ξ(s) = s(s-1)/2 · Γℝ(s) · ζ(s)` with `s(s-1)/2 · Γℝ(s)` analytic and nonvanishing there.
-/

open Complex

namespace GppXiZeroCounting

open GppLogDerivZeroFree

theorem xi_zero_ne : xi 0 ≠ 0 := by
  unfold xi
  simp

/-- Near a point `ρ` with `0 < Re ρ < 1`, `ξ(s) · Γℝ(s)⁻¹ = s(s-1)/2 · ζ(s)`. -/
theorem xi_mul_Gammaℝ_inv_eventuallyEq {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (fun s => xi s * (Gammaℝ s)⁻¹) =ᶠ[nhds ρ] fun s => (s * (s - 1) / 2) * riemannZeta s := by
  have hre : ∀ᶠ s in nhds ρ, 0 < s.re :=
    (continuous_re.continuousAt.eventually (lt_mem_nhds h0))
  have hre1 : ∀ᶠ s in nhds ρ, s.re < 1 :=
    (continuous_re.continuousAt.eventually (gt_mem_nhds h1))
  filter_upwards [hre, hre1] with s hs hs1r
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hg : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hz : riemannZeta s = completedRiemannZeta s / Gammaℝ s := riemannZeta_def_of_ne_zero hs0
  have hL : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
    have := completedRiemannZeta_eq s
    linear_combination this
  have hs1 : s ≠ 1 := fun h => by simp [h] at hs1r
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [hz, hL]
  unfold xi
  field_simp
  ring

theorem analyticAt_riemannZeta {ρ : ℂ} (h : ρ ≠ 1) : AnalyticAt ℂ riemannZeta ρ := by
  have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hd : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hd.analyticAt (hopen.mem_nhds h)

/-- **Orders of vanishing of `ξ` and `ζ` agree at every point of the open strip.** -/
theorem analyticOrderAt_xi_eq {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt xi ρ = analyticOrderAt riemannZeta ρ := by
  have hρ1 : ρ ≠ 1 := fun h => by simp [h] at h1
  have hxi : AnalyticAt ℂ xi ρ := differentiable_xi.analyticAt ρ
  have hinv : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) ρ :=
    differentiable_Gammaℝ_inv.analyticAt ρ
  have hinv0 : analyticOrderAt (fun s => (Gammaℝ s)⁻¹) ρ = 0 := by
    rw [hinv.analyticOrderAt_eq_zero]
    exact inv_ne_zero (Gammaℝ_ne_zero_of_re_pos h0)
  have hp : AnalyticAt ℂ (fun s : ℂ => s * (s - 1) / 2) ρ := by fun_prop
  have hp0 : analyticOrderAt (fun s : ℂ => s * (s - 1) / 2) ρ = 0 := by
    rw [hp.analyticOrderAt_eq_zero]
    have hρ0 : ρ ≠ 0 := fun h => by simp [h] at h0
    have : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
    exact div_ne_zero (mul_ne_zero hρ0 this) two_ne_zero
  have hz := analyticAt_riemannZeta hρ1
  have e1 : analyticOrderAt (fun s => xi s * (Gammaℝ s)⁻¹) ρ = analyticOrderAt xi ρ := by
    have := analyticOrderAt_mul hxi hinv
    rw [hinv0, add_zero] at this
    exact this
  have e2 : analyticOrderAt (fun s => (s * (s - 1) / 2) * riemannZeta s) ρ
      = analyticOrderAt riemannZeta ρ := by
    have := analyticOrderAt_mul hp hz
    rw [hp0, zero_add] at this
    exact this
  rw [← e1, ← e2]
  exact analyticOrderAt_congr (xi_mul_Gammaℝ_inv_eventuallyEq h0 h1)

theorem analyticOrderAt_xi_ne_top (ρ : ℂ) : analyticOrderAt xi ρ ≠ ⊤ := by
  intro htop
  have hev : xi =ᶠ[nhds ρ] 0 := analyticOrderAt_eq_top.1 htop
  have hon : AnalyticOnNhd ℂ xi Set.univ := fun z _ => differentiable_xi.analyticAt z
  have hzero := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ ρ) hev
  have h0 : xi 0 = 0 := hzero (Set.mem_univ 0)
  exact xi_zero_ne h0

/-- The divisor of `ξ` on a closed ball is its (natural-number) order of vanishing. -/
theorem divisor_xi_apply {r : ℝ} {ρ : ℂ} (hρ : ρ ∈ Metric.closedBall (0 : ℂ) r) :
    MeromorphicOn.divisor xi (Metric.closedBall (0 : ℂ) r) ρ = (analyticOrderNatAt xi ρ : ℤ) := by
  have hon : AnalyticOnNhd ℂ xi (Metric.closedBall (0 : ℂ) r) :=
    fun z _ => differentiable_xi.analyticAt z
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hon hρ]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_xi_ne_top ρ)
  simp [analyticOrderNatAt, ← hn]

end GppXiZeroCounting
