import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Haar probability measure on ℤ_p

Real infrastructure toward Tate's-thesis local zeta integral computations (the p-adic
integral formula from the newly uploaded lecture notes). `PadicInt p` (ℤ_p) is a compact
topological additive group (`PadicInt.compactSpace`, in
`Mathlib.NumberTheory.Padics.ProperSpace`), so it carries a canonical normalized Haar
probability measure via Mathlib's general `MeasureTheory.Measure.addHaarMeasure`
construction, applied to the top positive-compact witness `⊤ = Set.univ` (available
generically for any compact, nonempty topological group). Not sourced from a specific
Golden Physics Project paper.
-/

namespace GppPadicHaar

open MeasureTheory

variable (p : ℕ) [Fact p.Prime]

noncomputable instance : MeasurableSpace (PadicInt p) := borel _

instance : BorelSpace (PadicInt p) := ⟨rfl⟩

/-- The canonical Haar probability measure on `ℤ_p`, normalized so `μ(ℤ_p) = 1`. -/
noncomputable def haarMeasure : Measure (PadicInt p) :=
  Measure.addHaarMeasure ⊤

/-- `haarMeasure` is left-invariant (needed by downstream users; `haarMeasure` is an
    opaque `def`, so typeclass search won't unfold it to find the generic instance for
    `Measure.addHaarMeasure` on its own). -/
instance : (haarMeasure p).IsAddLeftInvariant :=
  Measure.isAddLeftInvariant_addHaarMeasure ⊤

/-- **`ℤ_p` has total Haar measure 1**: the canonical additive Haar measure on the
    compact group `ℤ_p`, normalized against the top positive-compact witness
    `⊤ = Set.univ`, gives `μ(ℤ_p) = 1`. -/
theorem haarMeasure_univ : haarMeasure p (Set.univ : Set (PadicInt p)) = 1 := by
  unfold haarMeasure
  have hset : (Set.univ : Set (PadicInt p)) =
      (⊤ : TopologicalSpace.PositiveCompacts (PadicInt p)) := rfl
  rw [hset]
  exact Measure.addHaarMeasure_self

end GppPadicHaar
