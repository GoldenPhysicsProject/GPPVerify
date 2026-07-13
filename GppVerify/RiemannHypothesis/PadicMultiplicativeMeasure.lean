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

1. For fixed `a ≠ 0`, the map `f_a : x ↦ a⁻¹ * x` is a continuous additive group
   automorphism of `ℚ_p` (field multiplication distributes over `+`, and `f_a` is its own
   kind of inverse up to swapping `a ↔ a⁻¹`). Bundle it as a `ContinuousAddEquiv (Padic p)
   (Padic p)` (or the nearest matching Mathlib structure — the exact bundling of
   continuity-both-ways needs to be pinned down against the live source, since doc
   scrapes of its constructor were inconclusive).
2. `ContinuousAddEquiv.isAddHaarMeasure_map f_a (fieldHaarMeasure p)` gives that
   `Measure.map f_a (fieldHaarMeasure p)` is again an `IsAddHaarMeasure`.
3. Since `(Measure.map f_a μ) S = μ (f_a⁻¹' S) = μ (a • S)` for measurable `S`
   (unwinding `f_a`'s preimage), this pushforward measure is exactly `S ↦ μ(a • S)`.
4. By Haar-measure uniqueness up to a scalar (`Measure.addHaarMeasure_unique`, or the
   `haarScalarFactor` machinery in `Mathlib.MeasureTheory.Measure.Haar.Unique`), this
   pushforward equals `c(a) • μ` for some constant `c(a) ≥ 0`.
5. Pin `c(a)` down using the already-proven `GppPadicZetaIntegral.haarMeasure_span_pow`
   (`μ(pⁿℤ_p) = p⁻ⁿ`) at a generating case (e.g. `a = p`, `S =` the closed unit ball),
   then extend to every `a ≠ 0` via the valuation decomposition `a = u·pⁿ` (`u` a unit,
   `‖u‖ = 1`) and multiplicativity of `c`.

Not a quick add-on: comparable in scope to the entire earlier `ℤ_p`-side Haar-measure
sub-thread (`PadicHaarMeasure.lean` through `PadicFullZetaIntegral.lean`, five files).

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
