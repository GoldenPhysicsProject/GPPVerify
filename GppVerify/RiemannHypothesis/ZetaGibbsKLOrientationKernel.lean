import GppVerify.RiemannHypothesis.ZetaGibbsFisherStrict
import Mathlib.Tactic

/-!
# Pointwise kernel for directed-KL orientation

For `1 < β < γ`, pair `t` in the left half of `[β,γ]` with its reflection
`β + γ - t`.  Strict decrease of the genuine Gibbs Fisher metric then makes the
paired antisymmetric KL kernel strictly positive.  This is the pointwise core
needed for the subsequent integral proof of directed-KL orientation.
-/

namespace GppZetaGibbsKLOrientationKernel

open GppZetaGibbsFisher
open GppZetaGibbsFisherStrict

/-- Reflection across the midpoint of `[β,γ]`. -/
def reflect (β γ t : ℝ) : ℝ := β + γ - t

/-- A point in the strict left half is strictly below its reflection. -/
theorem lt_reflect_of_lt_midpoint
    {β γ t : ℝ} (ht : t < (β + γ) / 2) :
    t < reflect β γ t := by
  unfold reflect
  linarith

/-- The antisymmetric linear weight is positive on the strict left half. -/
theorem antisymWeight_pos_of_lt_midpoint
    {β γ t : ℝ} (ht : t < (β + γ) / 2) :
    0 < β + γ - 2 * t := by
  linarith

/-- Strict Fisher decrease under midpoint reflection. -/
theorem variance_reflect_lt
    {β γ t : ℝ}
    (hβ : 1 < β) (hβt : β ≤ t) (ht : t < (β + γ) / 2) :
    logEnergyVariance (reflect β γ t) < logEnergyVariance t := by
  have ht1 : 1 < t := lt_of_lt_of_le hβ hβt
  exact logEnergyVariance_strictAnti ht1 (lt_reflect_of_lt_midpoint ht)

/-- **Positive paired KL kernel.**  On the left half of the interval, the
positive antisymmetric weight multiplies a strictly positive Fisher-metric
difference. -/
theorem pairedKLFisherKernel_pos
    {β γ t : ℝ}
    (hβ : 1 < β) (hβt : β ≤ t) (ht : t < (β + γ) / 2) :
    0 < (β + γ - 2 * t) *
      (logEnergyVariance t - logEnergyVariance (reflect β γ t)) := by
  have hw : 0 < β + γ - 2 * t := antisymWeight_pos_of_lt_midpoint ht
  have hg :
      0 < logEnergyVariance t - logEnergyVariance (reflect β γ t) := by
    exact sub_pos.mpr (variance_reflect_lt hβ hβt ht)
  exact mul_pos hw hg

end GppZetaGibbsKLOrientationKernel

#print axioms GppZetaGibbsKLOrientationKernel.pairedKLFisherKernel_pos
