import GppVerify.RiemannHypothesis.PadicFieldHaarMeasure
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The multiplicative Haar measure on ℚ_p, as a density reweighting

Tate's-thesis local zeta integrals are stated against the *multiplicative* Haar measure
`d^×x` on `ℚ_p^×`, related to the additive Haar measure `dx` (`GppPadicField.fieldHaarMeasure`,
built in this thread) by the standard formula `d^×x = dx / ‖x‖`.

Rather than build `ℚ_p^×` as its own topological group (which would need continuity of
inversion on units and a fresh compact-with-nonempty-interior witness — genuinely new
infrastructure not attempted here), this file defines the multiplicative measure directly
on `ℚ_p` itself via `MeasureTheory.Measure.withDensity`, using the density
`x ↦ ‖x‖⁻¹` (in `ℝ≥0∞`). Since `withDensity` only needs the density function to be
measurable, this definition is fully justified on its own; the genuinely hard fact this
thread has not yet proved is that this measure is *multiplicatively* invariant
(`μ^×(a • S) = μ^×(S)` for `a ≠ 0`), which needs the additive Haar measure's scaling law
under multiplication by a field element (`μ(a • S) = ‖a‖ · μ(S)`) — Mathlib's
`Measure.addHaar_smul` is specific to finite-dimensional `ℝ`-vector spaces and does not
apply to `ℚ_p` acting on itself, so this scaling law would need to be derived from
Haar-measure uniqueness from scratch. Queued as follow-up work; **concrete plan**, refined
against real Mathlib names (confirmed to exist via direct lookup, not yet assembled into a
proof):

1. **Done** (`PadicScalingHaar.lean`): for fixed `a ≠ 0`, `scaleAddEquiv p a ha : ℚ_p ≃ₜ+
   ℚ_p` (`x ↦ a⁻¹ * x`) is a `ContinuousAddEquiv`, built via `{ Homeomorph.mulLeft₀ a⁻¹
   (inv_ne_zero ha) with map_add' := ... }`.
2. **Done**: `(scaleAddEquiv p a ha).isAddHaarMeasure_map (fieldHaarMeasure p)` gives that
   `Measure.map (scaleAddEquiv p a ha) (fieldHaarMeasure p)` is again an
   `IsAddHaarMeasure` — needed adding an explicit `(fieldHaarMeasure p).IsAddHaarMeasure`
   instance in `PadicFieldHaarMeasure.lean` first (same opaque-`def` reasoning as the
   `IsAddLeftInvariant` instance already there; `Measure.isAddHaarMeasure_addHaarMeasure`
   doesn't auto-unfold through the `def`).
3. **Done**: `map_scaleAddEquiv_apply` shows this pushforward is exactly
   `S ↦ μ((fun y => a*y) '' S)` for measurable `S`.
4. **Confirmed to exist, not yet used**: the exact uniqueness tool is
   `MeasureTheory.Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure_of_innerRegularCompactLTTop
   (μ' μ : Measure G) [μ.IsAddHaarMeasure] [IsFiniteMeasureOnCompacts μ'] [μ'.IsAddLeftInvariant]
   [μ.InnerRegularCompactLTTop] {s : Set G} (hs : MeasurableSet s) (h's : IsCompact (closure s)) :
   μ' s = μ'.addHaarScalarFactor μ • μ s` (`Mathlib.MeasureTheory.Measure.Haar.Unique`) — gives
   the scalar equation *at a chosen compact set `s`* directly (not just for integrals),
   which is exactly the form needed here.
5. **Genuine obstruction found, not yet resolved**: pinning the scalar via the *existing*
   `GppPadicZetaIntegral.haarMeasure_span_pow` fact (proved for `GppPadicHaar.haarMeasure`
   on `PadicInt p`, a *different* ambient space from `Padic p`) is not a free transfer.
   The natural attempt — push `haarMeasure` forward along the embedding `PadicInt p ↪
   Padic p` and compare to `fieldHaarMeasure` — fails the uniqueness theorem's own
   `[μ'.IsAddLeftInvariant]` hypothesis: that pushforward is only invariant under
   translation by elements *of* `ℤ_p`, not by every element of `ℚ_p`, since the embedding's
   domain is only `ℤ_p`. So the scalar for `a = p` needs an *independent* derivation, most
   plausibly by redoing the translation/coset-counting argument
   (`GppHaarSubgroupIndex.index_vadd_measure_eq_univ`'s technique) *natively* on `Padic p`
   — i.e. rebuilding the `pⁿℤ_p ⊆ ℤ_p` coset-partition argument for `fieldHaarMeasure`
   from scratch rather than transferring it. `Padic.norm_le_pow_iff_norm_lt_pow_add_one`
   (confirmed to exist, `Mathlib.NumberTheory.Padics.PadicNumbers`) is the natural
   norm-ball characterization to build that on. Not attempted yet.

Not a quick add-on: comparable in scope to the entire earlier `ℤ_p`-side Haar-measure
sub-thread (`PadicHaarMeasure.lean` through `PadicFullZetaIntegral.lean`, five files) —
now with steps 1–3 of 5 landed, and step 4's exact tool confirmed, but step 5's transfer
obstruction genuinely unresolved.

Not sourced from a specific Golden Physics Project paper.
-/

namespace GppPadicField

open MeasureTheory

variable (p : ℕ) [Fact p.Prime]

/-- The multiplicative-measure density `‖x‖⁻¹`, valued in `ℝ≥0∞`. -/
noncomputable def multiplicativeDensity (x : Padic p) : ENNReal := (ENNReal.ofReal ‖x‖)⁻¹

theorem measurable_multiplicativeDensity : Measurable (multiplicativeDensity p) :=
  (ENNReal.measurable_ofReal.comp continuous_norm.measurable).inv

/-- **The multiplicative Haar measure on `ℚ_p`** (as a measure on `ℚ_p` itself, vanishing
    identically on `{0}` since `‖0‖⁻¹ = ⊤` only contributes on the `fieldHaarMeasure`-null
    singleton `{0}`): `d^×x := dx / ‖x‖`. -/
noncomputable def multiplicativeMeasure : Measure (Padic p) :=
  (fieldHaarMeasure p).withDensity (multiplicativeDensity p)

end GppPadicField
