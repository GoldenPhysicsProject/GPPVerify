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
5. **First obstruction found (transfer via *pushforward* fails), then a real resolution
   path found (transfer via *pullback* instead)**: pinning the scalar via the *existing*
   `GppPadicZetaIntegral.haarMeasure_span_pow` fact (proved for `GppPadicHaar.haarMeasure`
   on `PadicInt p`, a *different* ambient space from `Padic p`) is not a free transfer via
   `Measure.map`. Pushing `haarMeasure` *forward* along the embedding `ι : PadicInt p ↪
   Padic p` and comparing to `fieldHaarMeasure` fails the uniqueness theorem's own
   `[μ'.IsAddLeftInvariant]` hypothesis: that pushforward is only invariant under
   translation by elements *of* `ℤ_p`, not by every element of `ℚ_p`, since `ι`'s domain is
   only `ℤ_p`.

   The fix: transfer via `Measure.comap` (*pullback*) instead of `Measure.map`. Define
   `ν := Measure.comap ι (fieldHaarMeasure p)`, a measure *on `PadicInt p`*. For `x :
   PadicInt p` and measurable `S`, `ν (x + S) = fieldHaarMeasure p (ι(x + S)) =
   fieldHaarMeasure p (ι x + ι '' S)` (`ι` additive) `= fieldHaarMeasure p (ι '' S) = ν S`,
   using `fieldHaarMeasure`'s *full* `ℚ_p`-invariance to translate by `ι x ∈ ℚ_p` — no
   domain restriction this time, since translating the *ambient* measure by any element of
   `ℚ_p` is always legitimate. This is the key fix over the pushforward attempt. Concretely:
   - `Measure.comap_apply` (`Mathlib.MeasureTheory.Measure.Comap`) needs `ι` injective and
     `∀ s, MeasurableSet s → MeasurableSet (ι '' s)`; the latter should follow from `ι`
     being a closed embedding (`Continuous.isClosedEmbedding`, confirmed to exist, since
     `PadicInt p` is compact and `Padic p` is Hausdorff) composed with the fact that the
     closed unit ball is *clopen* in `ℚ_p` (standard non-archimedean fact — an ultrametric
     ball is always clopen), giving a genuine `MeasurableEmbedding`. Not yet confirmed
     which exact Mathlib lemma bridges "closed embedding with clopen image" to
     `MeasurableEmbedding`.
   - `ν Set.univ = fieldHaarMeasure p (Set.range ι) = fieldHaarMeasure p (closedBall 0 1) =
     1` (via the already-proven `fieldHaarMeasure_closedBall`), given `Set.range ι =
     closedBall 0 1` (should be close to definitional, since `PadicInt p` is essentially
     `{x : Padic p // ‖x‖ ≤ 1}`) — makes `ν` a probability measure.
   - `ν` should also inherit `IsAddHaarMeasure` (finite-on-compacts is free since `ι` is
     continuous; positive-on-opens needs the *same* clopen-ness fact above, since subspace
     opens of a clopen set are genuinely open in the ambient space).
   - Then `MeasureTheory.Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure` (confirmed
     signature: `(μ' μ : Measure G) [μ.IsAddHaarMeasure] [μ'.IsAddHaarMeasure]
     [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] : μ' = μ`,
     `Mathlib.MeasureTheory.Measure.Haar.Unique`) gives `ν = haarMeasure p` outright — full
     measure equality, not just at one set — since both are probability Haar measures on
     the *same* (compact) group `PadicInt p`. This sidesteps the general scalar-factor
     machinery of step 4 entirely for this transfer.
   - Combined with `Measure.comap_apply`, this gives `fieldHaarMeasure p (ι '' S) =
     haarMeasure p S` for every measurable `S ⊆ PadicInt p` — in particular at `S :=
     Ideal.span {p^n}`, using `ι '' (Ideal.span{p^n}) = closedBall 0 (p^{-n})` (via
     `PadicInt.norm_le_pow_iff_mem_span_pow` plus `ι` preserving the norm), directly gives
     `fieldHaarMeasure p (closedBall 0 (p^{-n})) = haarMeasure_span_pow`'s value `(p^n)⁻¹`
     — reusing the already-proven fact via this bridge, rather than re-deriving it from
     scratch.

   Each individual piece above has at least one plausible confirmed Mathlib anchor, but
   several (the measurable-embedding bridge, the clopen-ness lemma name, the exact
   `IsAddHaarMeasure`-transport argument) were not independently compiler-verified before
   this thread paused; assembling all of them correctly in one pass is genuinely uncertain
   and was not attempted blind.

Not a quick add-on: comparable in scope to the entire earlier `ℤ_p`-side Haar-measure
sub-thread (`PadicHaarMeasure.lean` through `PadicFullZetaIntegral.lean`, five files) —
now with steps 1–3 of 5 landed, step 4's exact tool confirmed, and step 5 upgraded from
"obstruction, no known fix" to "a complete resolution path found and precisely specified,
not yet executed."

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
