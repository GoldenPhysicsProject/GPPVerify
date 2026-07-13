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
Haar-measure uniqueness (`Measure.addHaarMeasure_unique`) from scratch. That derivation is
queued as follow-up work, not attempted here.

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
