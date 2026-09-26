import GppVerify.CelestialHolography.RegulatedBoxDilogDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Derivative cancellation kernel for the real Spence identity

The local dilogarithm series has now been differentiated directly on `0<x<1`.
Consequently the real Spence combination has derivative zero there, without any
functional-equation assumption.
-/

namespace GppRegulatedBoxSpenceDerivativeKernel

open GppRegulatedBoxDilogSeries
open GppRegulatedBoxDilogDerivative

/-- The real Spence combination built from the project's local dilogarithm series. -/
noncomputable def spenceCombination (x : ℝ) : ℝ :=
  li2Series x + li2Series (1 - x) + Real.log x * Real.log (1 - x)

/-- Exact derivative cancellation for the Spence combination from supplied local
derivative identities.  This algebraic kernel remains useful independently. -/
theorem spenceCombination_hasDerivAt_zero_of_derivatives
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hLx : HasDerivAt li2Series (-Real.log (1 - x) / x) x)
    (hL1x : HasDerivAt li2Series (-Real.log x / (1 - x)) (1 - x)) :
    HasDerivAt spenceCombination 0 x := by
  have hxne : x ≠ 0 := ne_of_gt hx0
  have h1xne : 1 - x ≠ 0 := by linarith
  have hone_sub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1 <;> ring
  have hL1x_comp :
      HasDerivAt (fun y : ℝ => li2Series (1 - y))
        ((-Real.log x / (1 - x)) * (-1)) x := by
    exact hL1x.comp x hone_sub
  have hlogx : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hxne
  have hlog1x :
      HasDerivAt (fun y : ℝ => Real.log (1 - y))
        ((1 / (1 - x)) * (-1)) x := by
    simpa [one_div, Function.comp_def] using
      (Real.hasDerivAt_log h1xne).comp x hone_sub
  have hprod :
      HasDerivAt (fun y : ℝ => Real.log y * Real.log (1 - y))
        ((1 / x) * Real.log (1 - x) +
          Real.log x * ((1 / (1 - x)) * (-1))) x := by
    exact hlogx.mul hlog1x
  have hsum := hLx.add hL1x_comp |>.add hprod
  have hzero :
      -Real.log (1 - x) / x +
          -Real.log x / (1 - x) * (-1) +
          ((1 / x) * Real.log (1 - x) +
            Real.log x * ((1 / (1 - x)) * (-1))) = 0 := by
    field_simp [hxne, h1xne]
    ring
  rw [hzero] at hsum
  simpa [spenceCombination] using hsum

/-- **Unconditional local Spence derivative cancellation.**  On `0<x<1`, the
project's actual local dilogarithm series makes the Spence combination stationary. -/
theorem spenceCombination_hasDerivAt_zero
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt spenceCombination 0 x := by
  have hLx := hasDerivAt_li2Series hx0 hx1
  have h1x0 : 0 < 1 - x := by linarith
  have h1x1 : 1 - x < 1 := by linarith
  have hL1x := hasDerivAt_li2Series h1x0 h1x1
  have hrewrite : 1 - (1 - x) = x := by ring
  rw [hrewrite] at hL1x
  exact spenceCombination_hasDerivAt_zero_of_derivatives hx0 hx1 hLx hL1x

end GppRegulatedBoxSpenceDerivativeKernel

#print axioms GppRegulatedBoxSpenceDerivativeKernel.spenceCombination_hasDerivAt_zero_of_derivatives
#print axioms GppRegulatedBoxSpenceDerivativeKernel.spenceCombination_hasDerivAt_zero
