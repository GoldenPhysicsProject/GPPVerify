import GppVerify.CelestialHolography.RaisedBoxRealMajorantIntegrability
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Raised-box real majorant: outer-kernel domination

After the exact `x3` and `x2` integrations, the singular part of the raised-box
majorant is proportional to

  x^(-δ) (1-x)^(2-δ)

on `0 ≤ x ≤ 1`.  For the physical range `δ < 1`, the second factor is at most
one.  Hence the outer kernel is dominated by the already-certified integrable
endpoint singularity `x^(-δ)`.  This avoids duplicating the complex Beta
calculation on the real side: exact Beta/Gamma evaluation and real DCT
integrability are kept as separate layers.
-/

namespace GppRaisedBoxRealOuterDomination

open MeasureTheory Real
open scoped Interval

/-- On the unit interval, the nonsingular affine factor appearing after the
inner two integrations is bounded by one throughout the physical range. -/
theorem post_middle_factor_le_one
    {δ x : ℝ} (hδ : δ < 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - x) ^ (2 - δ : ℝ) ≤ 1 := by
  apply Real.rpow_le_one
  · linarith
  · linarith
  · linarith

/-- Consequently the real outer Beta kernel is pointwise dominated by the
single endpoint singularity already known to be interval-integrable. -/
theorem outer_kernel_le_endpoint
    {δ x : ℝ} (hδ : δ < 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ^ (-δ : ℝ) * (1 - x) ^ (2 - δ : ℝ) ≤ x ^ (-δ : ℝ) := by
  have hfac : (1 - x) ^ (2 - δ : ℝ) ≤ 1 :=
    post_middle_factor_le_one hδ hx0 hx1
  have hxpow : 0 ≤ x ^ (-δ : ℝ) := Real.rpow_nonneg hx0 (-δ)
  nlinarith

/-- The outer real kernel is nonnegative on the unit interval. -/
theorem outer_kernel_nonneg
    {δ x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ x ^ (-δ : ℝ) * (1 - x) ^ (2 - δ : ℝ) := by
  have hbase : 0 ≤ 1 - x := by linarith
  have h1 : 0 ≤ x ^ (-δ : ℝ) := Real.rpow_nonneg hx0 (-δ)
  have h2 : 0 ≤ (1 - x) ^ (2 - δ : ℝ) := Real.rpow_nonneg hbase (2 - δ)
  exact mul_nonneg h1 h2

/-- DCT-ready norm domination: on the unit interval the norm of the real outer
kernel is bounded by the integrable endpoint singularity.  This is the exact
shape required by `Integrable.mono'`/dominated-convergence packaging. -/
theorem norm_outer_kernel_le_endpoint
    {δ x : ℝ} (hδ : δ < 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ‖x ^ (-δ : ℝ) * (1 - x) ^ (2 - δ : ℝ)‖ ≤ x ^ (-δ : ℝ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (outer_kernel_nonneg hx0 hx1)]
  exact outer_kernel_le_endpoint hδ hx0 hx1

end GppRaisedBoxRealOuterDomination

#print axioms GppRaisedBoxRealOuterDomination.post_middle_factor_le_one
#print axioms GppRaisedBoxRealOuterDomination.outer_kernel_le_endpoint
#print axioms GppRaisedBoxRealOuterDomination.outer_kernel_nonneg
#print axioms GppRaisedBoxRealOuterDomination.norm_outer_kernel_le_endpoint
