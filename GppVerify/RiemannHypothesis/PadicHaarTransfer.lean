import GppVerify.RiemannHypothesis.PadicZetaIntegral
import GppVerify.RiemannHypothesis.PadicShellMeasure
import GppVerify.RiemannHypothesis.PadicFieldHaarMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Transferring `haarMeasure_span_pow` from `ℤ_p` to `ℚ_p`

Step 5 of the `ℚ_p^×`-scaling-law plan (`PadicMultiplicativeMeasure.lean`), executed: the
already-proven `GppPadicZetaIntegral.haarMeasure_span_pow` (`μ(pⁿℤ_p) = p⁻ⁿ`, proved for
`GppPadicHaar.haarMeasure` living on `PadicInt p`) is transferred to `fieldHaarMeasure`
(living on `Padic p`) via `Measure.comap` along the inclusion `ι : ℤ_p ↪ ℚ_p`.

The key fact making this work (found after an earlier *pushforward* attempt failed): the
**pullback** `(fieldHaarMeasure p).comap ι` is invariant under all of `ℤ_p`'s own
translations using `fieldHaarMeasure`'s *full* `ℚ_p`-invariance — no domain restriction,
unlike pushing forward. Since `ℤ_p` is *clopen* in `ℚ_p` (a standard non-archimedean fact,
`IsUltrametricDist.isOpen_closedBall`), `ι` is an *open* embedding, and Mathlib's
`IsAddHaarMeasure.comap` (`Mathlib.MeasureTheory.Group.Measure`) packages exactly this
pullback-along-an-open-embedding argument into an instance. The pullback is then a
*probability* Haar measure on `ℤ_p` (total mass 1, matching `haarMeasure`'s own
normalization), so `isAddHaarMeasure_eq_of_isProbabilityMeasure`
(`Mathlib.MeasureTheory.Measure.Haar.Unique`) identifies it with `haarMeasure` outright.

Not sourced from a specific Golden Physics Project paper.
-/

namespace GppPadicField

open MeasureTheory
open scoped ENNReal

variable (p : ℕ) [Fact p.Prime]

/-- The inclusion `ℤ_p ↪ ℚ_p`, bundled as an additive monoid homomorphism. The coercion is
    definitionally additive (`PadicInt p`'s ring structure is inherited pointwise from
    `Padic p`), so both hom laws close by `rfl`. -/
def coeAddHom : PadicInt p →+ Padic p where
  toFun := (↑)
  map_zero' := rfl
  map_add' := fun _ _ => rfl

@[simp] theorem coeAddHom_apply (x : PadicInt p) : coeAddHom p x = (x : Padic p) := rfl

theorem range_coeAddHom :
    Set.range (coeAddHom p) = Metric.closedBall (0 : Padic p) 1 := by
  ext x
  simp only [coeAddHom_apply, Set.mem_range, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨y, rfl⟩; exact y.2
  · intro hx; exact ⟨⟨x, hx⟩, rfl⟩

/-- `ℤ_p ↪ ℚ_p` is an *open* embedding: it's the canonical subtype embedding (hence an
    embedding), and its range — the closed unit ball — is open, since closed balls of
    nonzero radius in an ultrametric space are clopen. -/
theorem isOpenEmbedding_coeAddHom : Topology.IsOpenEmbedding (coeAddHom p) := by
  refine ⟨Topology.IsEmbedding.subtypeVal, ?_⟩
  rw [range_coeAddHom]
  exact IsUltrametricDist.isOpen_closedBall (0 : Padic p) one_ne_zero

/-- The pullback of `fieldHaarMeasure` along the inclusion is again an additive Haar
    measure on `ℤ_p` — Mathlib's `IsAddHaarMeasure.comap` packages the whole
    pullback-along-an-open-embedding argument. -/
instance isAddHaarMeasure_comap :
    ((fieldHaarMeasure p).comap (coeAddHom p)).IsAddHaarMeasure :=
  MeasureTheory.Measure.IsAddHaarMeasure.comap (fieldHaarMeasure p)
    (isOpenEmbedding_coeAddHom p)

theorem comap_apply {S : Set (PadicInt p)} (hS : MeasurableSet S) :
    (fieldHaarMeasure p).comap (coeAddHom p) S = fieldHaarMeasure p (coeAddHom p '' S) :=
  Measure.comap_apply (coeAddHom p) (isOpenEmbedding_coeAddHom p).injective
    (fun s hs =>
      (isOpenEmbedding_coeAddHom p).measurableEmbedding.measurableSet_image.mpr hs)
    _ hS

/-- The pullback has total mass 1 (matching `fieldHaarMeasure`'s value on the closed unit
    ball, `fieldHaarMeasure_closedBall`), so it's a probability measure. -/
instance isProbabilityMeasure_comap :
    IsProbabilityMeasure ((fieldHaarMeasure p).comap (coeAddHom p)) := by
  constructor
  rw [comap_apply p MeasurableSet.univ, Set.image_univ, range_coeAddHom]
  exact fieldHaarMeasure_closedBall p

instance isProbabilityMeasure_haarMeasure : IsProbabilityMeasure (GppPadicHaar.haarMeasure p) := by
  constructor
  exact GppPadicHaar.haarMeasure_univ p

/-- **The transfer**: two probability Haar measures on the same (compact) group `ℤ_p`
    coincide. -/
theorem comap_eq_haarMeasure :
    (fieldHaarMeasure p).comap (coeAddHom p) = GppPadicHaar.haarMeasure p :=
  MeasureTheory.Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- `fieldHaarMeasure` and `haarMeasure` agree, via the embedding, on every measurable
    subset of `ℤ_p`. -/
theorem fieldHaarMeasure_image {S : Set (PadicInt p)} (hS : MeasurableSet S) :
    fieldHaarMeasure p (coeAddHom p '' S) = GppPadicHaar.haarMeasure p S := by
  rw [← comap_apply p hS, comap_eq_haarMeasure]

/-- The image of the shell-defining span under the embedding is exactly the corresponding
    closed ball in `ℚ_p`. -/
theorem image_span_pow_eq_closedBall (n : ℕ) :
    coeAddHom p '' (Ideal.span {(p : PadicInt p) ^ n} : Set (PadicInt p)) =
      Metric.closedBall (0 : Padic p) ((p : ℝ) ^ (-(n : ℤ))) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hpn1 : (1 : ℝ) ≤ (p : ℝ) ^ n := one_le_pow₀ hp1
  have hle1 : (p : ℝ) ^ (-(n : ℤ)) ≤ 1 := by
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ hpn1
  ext x
  simp only [coeAddHom_apply, Set.mem_image, Metric.mem_closedBall, dist_zero_right,
    SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← PadicInt.norm_def]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow y n).mpr hy
  · intro hx
    have hx1 : ‖x‖ ≤ 1 := le_trans hx hle1
    refine ⟨⟨x, hx1⟩, (PadicInt.norm_le_pow_iff_mem_span_pow ⟨x, hx1⟩ n).mp ?_, rfl⟩
    rw [PadicInt.norm_def]
    exact hx

/-- **The payoff**: `fieldHaarMeasure p (pⁿ ℤ_p) = p⁻ⁿ`, transferred from the
    already-proven `GppPadicZetaIntegral.haarMeasure_span_pow` via the embedding — the
    fact this whole thread has been building toward. -/
theorem fieldHaarMeasure_span_pow (n : ℕ) :
    fieldHaarMeasure p (Metric.closedBall (0 : Padic p) ((p : ℝ) ^ (-(n : ℤ)))) =
      ((p : ℝ≥0∞) ^ n)⁻¹ := by
  rw [← image_span_pow_eq_closedBall,
      fieldHaarMeasure_image p (GppPadicShell.measurableSet_span_pow p n),
      GppPadicZetaIntegral.haarMeasure_span_pow]

end GppPadicField
