/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.AdelicFundamentalDomain
import GppVerify.Upstream.RatFiniteAdeleRingHaar

/-!
# The covolume of `ℚ` in the adeles (GP4)

On the adele carrier `AQ = ℝ × 𝔸_f`, take the Haar measure `adeleHaar` equal to Lebesgue measure at
infinity times the Haar measure on `𝔸_f` normalized by `vol(∏ ℤ_v) = 1`
(`Rat.FiniteAdeleRing.haar`, upstream module). This is the normalization pinned by Turbo
(GPP-bridge PR #11, 6730857794). The covolume, the measure of the fundamental domain
`[0, 1) × ∏ ℤ_v` of GP3, is then `1` (`covolume_eq_one`): it is computed from the
normalizations, not assumed.

Governing specification: Principal series's global Tate statement sheet (GPP-bridge branch
`principal-series/global-tate-statements` at `77d5b43`, §4, GP4), audited PASS by Turbo.
-/

open MeasureTheory

namespace GlobalTate.Poisson

/-- Haar measure on the adeles: Lebesgue × the `vol(∏ ℤ_v) = 1` Haar measure on `𝔸_f`. -/
noncomputable def adeleHaar : Measure AQ := (volume : Measure ℝ).prod Rat.FiniteAdeleRing.haar

/-- The covolume of `ℚ` in the adeles: the measure of the fundamental domain. -/
noncomputable def covolume : ENNReal := adeleHaar fundBox

theorem intBox_eq_integralAdeles : intBox = Rat.FiniteAdeleRing.integralAdeles := rfl

/-- **GP4.** The covolume of `ℚ` in the adeles is `1`. -/
theorem covolume_eq_one : covolume = 1 := by
  unfold covolume adeleHaar fundBox
  rw [Measure.prod_prod, Real.volume_Ico, intBox_eq_integralAdeles,
    Rat.FiniteAdeleRing.haar_integralAdeles]
  simp

end GlobalTate.Poisson
