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

end Complex
