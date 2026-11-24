import GppVerify.RiemannHypothesis.ShiftPresentation
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The shift series is in `L²`

`Φ_p g = Σ_{m≥0} p^{−m/2} g(· − m log p)` (generic form `shiftSeries q ℓ g`) is a continuous function in
`L²(ℝ)` for continuous compactly supported `g`, `ℓ`, `0 < q < 1`. This is the membership that lets
`‖Φ_p g‖²` (`phiNormSq`, an integral) be the squared norm of an element of `L²` — the ingredient behind
the two-positive-space form of OB-6 (`TwoSpaceForm.lean`).

Proof: continuity from `continuous_tsum` with the geometric bound; `Φ² = Σ_{(m,m')} term` integrates by the
same summable-norm bound as in `ShiftSeriesNorm`, now used for *integrability* (finite `lintegral`) rather
than only for the value. No `sorry`, no axiom.
-/

open MeasureTheory
open GppArithmeticReflection

noncomputable section

namespace GppShiftPresentation

variable {g : ℝ → ℝ} {q ℓ : ℝ}

theorem continuous_shiftSeries (hg : Continuous g) (hc : HasCompactSupport g)
    (hq0 : 0 < q) (hq1 : q < 1) : Continuous (shiftSeries q ℓ g) := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  refine continuous_tsum (u := fun m : ℕ => q ^ m * B) (fun m => ?_)
    ((summable_geometric_of_lt_one hq0.le hq1).mul_right B) (fun m y => ?_)
  · exact continuous_const.mul (hg.comp (continuous_id.sub continuous_const))
  · rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hq0]
    have := hB (y - m * ℓ)
    simp only [Real.norm_eq_abs] at this
    exact mul_le_mul_of_nonneg_left this (by positivity)

theorem continuous_term (hg : Continuous g) (z : ℕ × ℕ) : Continuous (term q ℓ g z) := by
  unfold term
  exact (continuous_const.mul (hg.comp (continuous_id.sub continuous_const))).mul
    (continuous_const.mul (hg.comp (continuous_id.sub continuous_const)))

/-- The squared shift series is integrable. -/
theorem integrable_shiftSeries_sq (hg : Continuous g) (hc : HasCompactSupport g)
    (hq0 : 0 < q) (hq1 : q < 1) : Integrable (fun y => (shiftSeries q ℓ g y) ^ 2) := by
  obtain ⟨D, hD⟩ := term_norm_integral_le (ℓ := ℓ) hg hc hq0
  have hsum : Summable fun z : ℕ × ℕ => ∫ y, ‖term q ℓ g z y‖ := by
    refine Summable.of_nonneg_of_le (fun z => integral_nonneg fun y => norm_nonneg _) hD ?_
    exact (summable_geom_pair hq0 hq1).mul_right D
  have hmeas : AEStronglyMeasurable (fun y => (shiftSeries q ℓ g y) ^ 2) volume :=
    ((continuous_shiftSeries hg hc hq0 hq1).pow 2).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hint : ∀ z, Integrable (term q ℓ g z) := fun z => term_integrable hg hc z
  calc ∫⁻ y, ‖(shiftSeries q ℓ g y) ^ 2‖ₑ
      = ∫⁻ y, ‖∑' z : ℕ × ℕ, term q ℓ g z y‖ₑ := by
        refine lintegral_congr fun y => ?_
        rw [shiftSeries_sq hg hc hq0 hq1]
    _ ≤ ∫⁻ y, ∑' z : ℕ × ℕ, ‖term q ℓ g z y‖ₑ :=
        lintegral_mono fun y => enorm_tsum_le_tsum_enorm
    _ = ∑' z : ℕ × ℕ, ∫⁻ y, ‖term q ℓ g z y‖ₑ :=
        lintegral_tsum fun z => (hint z).1.enorm
    _ = ∑' z : ℕ × ℕ, ENNReal.ofReal (∫ y, ‖term q ℓ g z y‖) :=
        tsum_congr fun z => (ofReal_integral_norm_eq_lintegral_enorm (hint z)).symm
    _ = ENNReal.ofReal (∑' z : ℕ × ℕ, ∫ y, ‖term q ℓ g z y‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun z => integral_nonneg fun y => norm_nonneg _) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- **`Φ ∈ L²`.** -/
theorem memLp_shiftSeries (hg : Continuous g) (hc : HasCompactSupport g)
    (hq0 : 0 < q) (hq1 : q < 1) : MemLp (shiftSeries q ℓ g) 2 volume :=
  (memLp_two_iff_integrable_sq
    (continuous_shiftSeries hg hc hq0 hq1).aestronglyMeasurable).2
    (integrable_shiftSeries_sq hg hc hq0 hq1)

end GppShiftPresentation

#print axioms GppShiftPresentation.memLp_shiftSeries
