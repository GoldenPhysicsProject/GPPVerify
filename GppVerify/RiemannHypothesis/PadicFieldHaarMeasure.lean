import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Additive Haar measure on the full p-adic field ℚ_p

The first brick toward a genuine multiplicative Haar measure on `ℚ_p^×` (Tate's-thesis
local zeta integral in its full, unrestricted-domain form): the `GppPadicHaar.haarMeasure`
built earlier in this thread lives only on the compact subring `ℤ_p` (`PadicInt p`), where
the canonical `⊤ = Set.univ` witness works because the *whole space* is compact. `ℚ_p`
itself is only *locally* compact, so building its canonical (translation-invariant, up to
positive scalar) additive Haar measure needs an explicit compact-with-nonempty-interior
witness instead of `⊤`.

The natural, canonical choice — matching Tate's own normalization convention exactly — is
the closed unit ball `{x : ℚ_p | ‖x‖ ≤ 1}`, which is nothing but (the image of) `ℤ_p`
itself. Its compactness follows immediately from `Padic.instProperSpace`
(`Mathlib.NumberTheory.Padics.ProperSpace`): a proper metric space's closed balls are
compact by definition/characterization, `isCompact_closedBall`. Its interior is nonempty
because it contains the (nonempty) open unit ball,
`Metric.ball_subset_interior_closedBall`.

Not sourced from a specific Golden Physics Project paper.
-/

namespace GppPadicField

open MeasureTheory

variable (p : ℕ) [Fact p.Prime]

noncomputable instance : MeasurableSpace (Padic p) := borel _

instance : BorelSpace (Padic p) := ⟨rfl⟩

/-- The closed unit ball `{x : ℚ_p | ‖x‖ ≤ 1}`, as a compact-with-nonempty-interior
    witness for building the canonical additive Haar measure on `ℚ_p`. Using this ball
    (rather than an arbitrary one) normalizes the resulting measure so that it assigns
    total mass 1 to exactly the set corresponding to `ℤ_p` — Tate's own convention. -/
noncomputable def unitBallPositiveCompacts : TopologicalSpace.PositiveCompacts (Padic p) where
  carrier := Metric.closedBall 0 1
  isCompact' := isCompact_closedBall 0 1
  interior_nonempty' :=
    ⟨0, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self one_pos)⟩

/-- The canonical additive Haar measure on `ℚ_p`, normalized so that the closed unit ball
    (i.e. `ℤ_p`) has measure 1. -/
noncomputable def fieldHaarMeasure : Measure (Padic p) :=
  Measure.addHaarMeasure (unitBallPositiveCompacts p)

/-- `fieldHaarMeasure` is left-invariant (needed by downstream users; `fieldHaarMeasure` is
    an opaque `def`, so typeclass search won't unfold it to find the generic instance for
    `Measure.addHaarMeasure` on its own). -/
instance : (fieldHaarMeasure p).IsAddLeftInvariant :=
  Measure.isAddLeftInvariant_addHaarMeasure (unitBallPositiveCompacts p)

/-- **`ℚ_p`'s canonical Haar measure gives the closed unit ball (`ℤ_p`) measure 1.** -/
theorem fieldHaarMeasure_closedBall :
    fieldHaarMeasure p (Metric.closedBall (0 : Padic p) 1) = 1 := by
  unfold fieldHaarMeasure
  exact Measure.addHaarMeasure_self

end GppPadicField
