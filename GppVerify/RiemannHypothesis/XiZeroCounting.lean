/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Order
import GppVerify.RiemannHypothesis.LogDerivativeZeroFree

/-!
# Explicit formula, stage E3b (part 1): multiplicities of `ξ` and `ζ` agree in the strip

For `0 < Re ρ < 1` the orders of vanishing of `ξ` and `ζ` at `ρ` coincide, because
`ξ(s) = s(s-1)/2 · Γℝ(s) · ζ(s)` with `s(s-1)/2 · Γℝ(s)` analytic and nonvanishing there.
-/

open Complex

namespace GppXiZeroCounting

open GppLogDerivZeroFree

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

end GppXiZeroCounting
