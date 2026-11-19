/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statements from Heart of the Cosmos / Grok)
-/
import Mathlib.Tactic
import GppVerify.RiemannHypothesis.OneSided

/-!
# Local Pringsheim–Landau theorem (Round 23 F10, `landau_local`)

Heart's F10 (Landau 1905; Widder, *The Laplace Transform*, Thm II.5b): for `f ≥ 0` whose Laplace
transform converges for `σ > σ_c` and diverges for `σ < σ_c`, the transform has no analytic
continuation to any neighbourhood of `σ_c`.

Turbo's Round 23 audit (Correction 2) located the form the Landau reduction (F12) needs: the
*local* one, where the continuation is only assumed on a neighbourhood of the real point `σ_c` —
not on the whole half-plane, which for the candidate `ξ′/ξ`-transform would presuppose the
zero-free half-plane. This module proves it from `landau_disc` (the Taylor-at-`σ_c + 1`/Tonelli
argument, factored out of `landau_full` in `OneSided.lean`):

* `landau_local`: if `h ≥ 0`, its Laplace transform converges above `σ_c`, and agrees there with a
  function `Hext` holomorphic on `ball(σ_c, δ) ∪ {Re z > σ_c}`, then it converges at every real `y`
  with `y > σ_c − min 1 (δ²/3)`.
* `pringsheim_no_continuation`: the filed F10 form. If additionally the transform diverges at every
  `τ < σ_c`, no such continuation exists.

Geometry: the disc `ball(σ_c + 1, 1 + r)` with `r = min 1 (δ²/3)` lies inside
`ball(σ_c, δ) ∪ {Re z > σ_c}`.

No zeta zero is an input; no `sorry`, no `axiom`.
-/

namespace GppHeartLandau

open MeasureTheory Set Complex

/-- The disc of radius `1 + r` about `σ + 1` lies in `ball(σ, δ) ∪ {Re > σ}` when `r ≤ 1`,
`3 r ≤ δ²`. -/
theorem ball_subset_union {σ δ r : ℝ} (hδ : 0 < δ) (hr0' : 0 ≤ r) (hr1 : r ≤ 1) (hr : 3 * r ≤ δ ^ 2) :
    Metric.ball ((σ + 1 : ℝ) : ℂ) (1 + r)
      ⊆ Metric.ball (σ : ℂ) δ ∪ {z : ℂ | σ < z.re} := by
  intro z hz
  by_cases hre : σ < z.re
  · exact Or.inr hre
  · left
    rw [not_lt] at hre
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    have h1 : ‖z - ((σ + 1 : ℝ) : ℂ)‖ ^ 2 < (1 + r) ^ 2 := by
      exact pow_lt_pow_left₀ hz (norm_nonneg _) two_ne_zero
    rw [Complex.sq_norm, Complex.normSq_apply] at h1
    have e1 : (z - ((σ + 1 : ℝ) : ℂ)).re = z.re - (σ + 1) := by simp
    have e2 : (z - ((σ + 1 : ℝ) : ℂ)).im = z.im := by simp
    rw [e1, e2] at h1
    have h2 : ‖z - (σ : ℂ)‖ ^ 2 < δ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have e3 : (z - (σ : ℂ)).re = z.re - σ := by simp
      have e4 : (z - (σ : ℂ)).im = z.im := by simp
      rw [e3, e4]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hδ.le h2

/-- **F10 (`landau_local`), local Pringsheim–Landau.** -/
theorem landau_local {h : ℝ → ℝ} {σc δ : ℝ} {Hext : ℂ → ℂ}
    (hpos : ∀ t, 0 ≤ h t) (hδ : 0 < δ)
    (hconv : ∀ τ : ℝ, σc < τ →
      IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ) : ℂ)) (Ioi 0) volume)
    (hHext : DifferentiableOn ℂ Hext (Metric.ball (σc : ℂ) δ ∪ {z : ℂ | σc < z.re}))
    (heq : ∀ z : ℂ, σc < z.re →
      Hext z = ∫ t : ℝ in Ioi 0, Complex.exp (-z * (t : ℂ)) * ((h t : ℝ) : ℂ)) :
    ∀ y : ℝ, σc - min 1 (δ ^ 2 / 3) < y →
      IntegrableOn (fun t : ℝ ↦ ((Real.exp (-y * t) * h t : ℝ) : ℂ)) (Ioi 0) volume := by
  intro y hy
  by_cases hlt : σc < y
  · exact hconv y hlt
  · rw [not_lt] at hlt
    set r : ℝ := min 1 (δ ^ 2 / 3) with hr_def
    have hr1 : r ≤ 1 := min_le_left _ _
    have hr3 : 3 * r ≤ δ ^ 2 := by
      have := min_le_right 1 (δ ^ 2 / 3)
      linarith
    have hsub := ball_subset_union (σ := σc) hδ (le_min zero_le_one (by positivity)) hr1 hr3
    exact RhWaveLean.landau_disc hpos hconv (x := σc + 1) (R := 1 + r)
      (by linarith) (hHext.mono hsub) heq (by linarith) (by linarith)

/-- **F10 as filed.** If `h ≥ 0`, the Laplace transform converges for `τ > σc` and diverges for
every `τ < σc`, then the transform has no analytic continuation (agreeing with it on `Re z > σc`) to
`ball(σc, δ) ∪ {Re z > σc}` for any `δ > 0`. -/
theorem pringsheim_no_continuation {h : ℝ → ℝ} {σc : ℝ}
    (hpos : ∀ t, 0 ≤ h t)
    (hconv : ∀ τ : ℝ, σc < τ →
      IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ) : ℂ)) (Ioi 0) volume)
    (hdiv : ∀ τ : ℝ, τ < σc →
      ¬ IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * h t : ℝ) : ℂ)) (Ioi 0) volume)
    {δ : ℝ} (hδ : 0 < δ) :
    ¬ ∃ Hext : ℂ → ℂ,
        DifferentiableOn ℂ Hext (Metric.ball (σc : ℂ) δ ∪ {z : ℂ | σc < z.re}) ∧
        ∀ z : ℂ, σc < z.re →
          Hext z = ∫ t : ℝ in Ioi 0, Complex.exp (-z * (t : ℂ)) * ((h t : ℝ) : ℂ) := by
  rintro ⟨Hext, hHext, heq⟩
  have hr : 0 < min 1 (δ ^ 2 / 3) := lt_min one_pos (by positivity)
  have := landau_local hpos hδ hconv hHext heq (σc - min 1 (δ ^ 2 / 3) / 2) (by linarith)
  exact hdiv _ (by linarith) this

end GppHeartLandau

#print axioms GppHeartLandau.landau_local
#print axioms GppHeartLandau.pringsheim_no_continuation
