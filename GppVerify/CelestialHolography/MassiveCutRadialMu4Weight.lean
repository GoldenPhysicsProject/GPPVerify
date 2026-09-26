import Mathlib.Analysis.SpecialFunctions.Hyperbolic.Basic
import Mathlib.Tactic

/-!
# Massive celestial radial weight for the D-dimensional MHV cut

For a two-particle cut with channel mass `M` and transverse mass `mu`, the fixed-radius
massive celestial shell is parametrized by

  mu = M / (2 cosh r).

The rational one-loop box sector in D-dimensional unitarity carries a `mu^4` numerator.
This file records its exact radial form

  mu^4 = M^4 / (16 cosh(r)^4).

This is only the radial change of variables. It does not assert a complete Yang--Mills
state sum, triangle/bubble subtraction, or a dispersion theorem.
-/

namespace GppMassiveCutRadialMu4Weight

/-- Transverse mass expressed in the fixed-radius massive celestial chart. -/
noncomputable def muFromRadius (M r : ℝ) : ℝ :=
  M / (2 * Real.cosh r)

/-- The fourth power of the transverse mass is the exact `cosh^{-4}` radial weight. -/
theorem muFromRadius_pow_four (M r : ℝ) :
    muFromRadius M r ^ 4 = M ^ 4 / (16 * Real.cosh r ^ 4) := by
  have hc : Real.cosh r ≠ 0 := ne_of_gt (Real.cosh_pos r)
  unfold muFromRadius
  field_simp [hc]
  ring

/-- The D-dimensional rational box radial weight is nonnegative. -/
theorem muFromRadius_pow_four_nonneg (M r : ℝ) :
    0 ≤ muFromRadius M r ^ 4 := by
  positivity

/-- For positive channel mass, the transverse mass in this chart is strictly positive. -/
theorem muFromRadius_pos {M r : ℝ} (hM : 0 < M) :
    0 < muFromRadius M r := by
  unfold muFromRadius
  positivity

/-- Any shell relation `mu = M/(2 cosh r)` transports the physical `mu^4` numerator
exactly to the celestial radial weight. -/
theorem shell_mu_pow_four
    {M mu r : ℝ} (hmu : mu = muFromRadius M r) :
    mu ^ 4 = M ^ 4 / (16 * Real.cosh r ^ 4) := by
  rw [hmu, muFromRadius_pow_four]

end GppMassiveCutRadialMu4Weight

#print axioms GppMassiveCutRadialMu4Weight.muFromRadius_pow_four
#print axioms GppMassiveCutRadialMu4Weight.shell_mu_pow_four
