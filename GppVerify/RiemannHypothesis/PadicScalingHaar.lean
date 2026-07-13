import GppVerify.RiemannHypothesis.PadicFieldHaarMeasure
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# The pushforward of `fieldHaarMeasure` under scaling is again a Haar measure

First concrete step toward the `ℚ_p^×`-scaling law documented in
`PadicMultiplicativeMeasure.lean`: for `a ≠ 0`, multiplication by `a⁻¹` is a continuous
additive automorphism of `ℚ_p` (field multiplication distributes over `+`, and it's a
homeomorphism since `a⁻¹ ≠ 0`, via `Homeomorph.mulLeft₀`). Pushing `fieldHaarMeasure`
forward along it is therefore again an additive Haar measure
(`ContinuousAddEquiv.isAddHaarMeasure_map`), and that pushforward is exactly the
set-function `S ↦ μ(a • S)`.

What remains (steps 4–5 of the plan in `PadicMultiplicativeMeasure.lean`, not attempted
here): invoking Haar-measure uniqueness up to a scalar to conclude this pushforward
equals `c(a) • μ`, and pinning `c(a) = ‖a‖` down via `haarMeasure_span_pow`. Not sourced
from a specific Golden Physics Project paper.
-/

namespace GppPadicField

open MeasureTheory

variable (p : ℕ) [Fact p.Prime]

/-- Multiplication by `a⁻¹` (`a ≠ 0`), as a continuous additive automorphism of `ℚ_p`:
    the algebraic content is `map_add'` (field multiplication distributes over `+`); the
    topological content is entirely supplied by `Homeomorph.mulLeft₀`. -/
noncomputable def scaleAddEquiv (a : Padic p) (ha : a ≠ 0) :
    ContinuousAddEquiv (Padic p) (Padic p) :=
  { Homeomorph.mulLeft₀ a⁻¹ (inv_ne_zero ha) with
    map_add' := fun x y => by
      show a⁻¹ * (x + y) = a⁻¹ * x + a⁻¹ * y
      ring }

@[simp] theorem scaleAddEquiv_apply (a : Padic p) (ha : a ≠ 0) (x : Padic p) :
    scaleAddEquiv p a ha x = a⁻¹ * x := rfl

/-- The pushforward of `fieldHaarMeasure` under `scaleAddEquiv` is again an additive Haar
    measure on `ℚ_p`. -/
instance isAddHaarMeasure_map_scaleAddEquiv (a : Padic p) (ha : a ≠ 0) :
    (Measure.map (scaleAddEquiv p a ha) (fieldHaarMeasure p)).IsAddHaarMeasure :=
  ContinuousAddEquiv.isAddHaarMeasure_map (scaleAddEquiv p a ha) (fieldHaarMeasure p)

/-- Unwinding the pushforward: `(Measure.map (scaleAddEquiv p a ha) μ) S = μ ((a * ·) '' S)`
    for every measurable `S` — i.e. this pushforward measure *is* the set-function
    `S ↦ μ(a • S)` whose scaling behaviour we ultimately want to pin down. -/
theorem map_scaleAddEquiv_apply (a : Padic p) (ha : a ≠ 0) {S : Set (Padic p)}
    (hS : MeasurableSet S) :
    Measure.map (scaleAddEquiv p a ha) (fieldHaarMeasure p) S =
      fieldHaarMeasure p ((fun y => a * y) '' S) := by
  rw [Measure.map_apply (scaleAddEquiv p a ha).continuous.measurable hS]
  congr 1
  ext x
  simp only [Set.mem_preimage, scaleAddEquiv_apply, Set.mem_image]
  constructor
  · intro hx
    exact ⟨a⁻¹ * x, hx, by field_simp⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [show a⁻¹ * (a * y) = y by field_simp]

end GppPadicField
