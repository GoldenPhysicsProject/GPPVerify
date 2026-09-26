import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Compatibility bridge for the Lean 4.19 Mathlib interval-integral API.

The project previously imported `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`, a module
that is not present in the pinned Mathlib revision.  The three names below are the real-valued
multiplicative specializations of the current `smul_integral_comp_*` theorems used by the causal
heat-boundary calculation.  Keeping the bridge isolated makes the mathematical dependency
explicit and removable when the caller is migrated to the current API directly.
-/

namespace intervalIntegral

@[simp] theorem mul_integral_comp_add_mul
    (f : ℝ → ℝ) (c d : ℝ) {a b : ℝ} :
    c * (∫ x in a..b, f (d + c * x)) =
      ∫ x in d + c * a..d + c * b, f x := by
  simpa [smul_eq_mul] using
    (smul_integral_comp_add_mul f c d (a := a) (b := b))

@[simp] theorem mul_integral_comp_mul_sub
    (f : ℝ → ℝ) (c d : ℝ) {a b : ℝ} :
    c * (∫ x in a..b, f (c * x - d)) =
      ∫ x in c * a - d..c * b - d, f x := by
  simpa [smul_eq_mul] using
    (smul_integral_comp_mul_sub f c d (a := a) (b := b))

@[simp] theorem mul_integral_comp_mul_add
    (f : ℝ → ℝ) (c d : ℝ) {a b : ℝ} :
    c * (∫ x in a..b, f (c * x + d)) =
      ∫ x in c * a + d..c * b + d, f x := by
  simpa [smul_eq_mul] using
    (smul_integral_comp_mul_add f c d (a := a) (b := b))

end intervalIntegral
