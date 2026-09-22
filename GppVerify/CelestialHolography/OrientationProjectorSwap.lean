import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import GppVerify.CelestialHolography.OrientationGooglyCore

/-!
# Generic chiral-projector exchange under four-orientation reversal

The previous orientation core proves that a pure self-dual field becomes anti-self-dual
when the four-dimensional orientation is reversed.  The stronger statement needed for a
generic nonlinear curvature field is projector-level and does not require purity.

On complexified Lorentzian two-forms, with Hodge eigenvalues `+i` and `-i`, define

  P_plus  = 1/2 (1 - i star),
  P_minus = 1/2 (1 + i star).

Reversing orientation changes `star` to `-star`, while leaving the underlying two-form
itself fixed.  Therefore, for every field `F`,

  P_plus[-o](F)  = P_minus[o](F),
  P_minus[-o](F) = P_plus[o](F).

This is a relabelling/exchange of the two chiral components of the SAME field.  It does
not generate a missing independent curvature component from a pure chiral solution.

No assumption `star^2=-1` is needed for the exchange identities themselves; that
assumption is only needed when one wants to prove the maps are genuine eigenspace
projectors.
-/

namespace GppOrientationProjectorSwap

open GppOrientationGoogly

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- `+i` Hodge-sector projector formula. -/
noncomputable def projPlus (star : V → V) (F : V) : V :=
  ((1 : ℂ) / 2) • (F - Complex.I • star F)

/-- `-i` Hodge-sector projector formula. -/
noncomputable def projMinus (star : V → V) (F : V) : V :=
  ((1 : ℂ) / 2) • (F + Complex.I • star F)

/-- Orientation reversal exchanges the generic `+` component with the old `-` component. -/
theorem projPlus_reversed_eq_projMinus (star : V → V) (F : V) :
    projPlus (reversedHodge star) F = projMinus star F := by
  simp [projPlus, projMinus, reversedHodge]

/-- And conversely the generic `-` component becomes the old `+` component. -/
theorem projMinus_reversed_eq_projPlus (star : V → V) (F : V) :
    projMinus (reversedHodge star) F = projPlus star F := by
  simp [projPlus, projMinus, reversedHodge]

/-- Ordered pair of chiral components relative to an orientation-dependent Hodge star. -/
noncomputable def chiralComponents (star : V → V) (F : V) : V × V :=
  (projPlus star F, projMinus star F)

/-- Main generic-curvature theorem: reversing the four-orientation swaps the two chiral
components of the same underlying field. -/
theorem chiralComponents_reversed_swap (star : V → V) (F : V) :
    chiralComponents (reversedHodge star) F =
      (projMinus star F, projPlus star F) := by
  simp [chiralComponents, projPlus_reversed_eq_projMinus,
    projMinus_reversed_eq_projPlus]

/-- Reversing orientation twice restores the same ordered chiral decomposition. -/
theorem chiralComponents_double_reversal (star : V → V) (F : V) :
    chiralComponents (reversedHodge (reversedHodge star)) F =
      chiralComponents star F := by
  rw [reversedHodge_involution]

/-- The pure-sector theorem is recovered immediately from the projector-level exchange:
if the old `+` component vanishes, it is the new `-` component that vanishes, and vice
versa.  This statement is phrased purely as component equality and therefore does not
assume additional Hodge identities. -/
theorem zero_component_exchanges
    (star : V → V) (F : V) :
    (projPlus star F = 0 ↔ projMinus (reversedHodge star) F = 0) ∧
    (projMinus star F = 0 ↔ projPlus (reversedHodge star) F = 0) := by
  constructor
  · rw [projMinus_reversed_eq_projPlus]
  · rw [projPlus_reversed_eq_projMinus]

end GppOrientationProjectorSwap
