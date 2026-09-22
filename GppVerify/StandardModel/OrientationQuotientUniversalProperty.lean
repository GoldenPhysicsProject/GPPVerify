import Mathlib.Tactic
import GppVerify.StandardModel.OrientationMassTime

/-!
# Universal property of the diagonal orientation quotient

The finite orientation carrier is `Bool × Bool`, with the diagonal reversal

    D(q,t) = (!q,!t)

and relational character

    χ(q,t) = xor q t.

The existing finite theorem shows that two points have equal `χ` exactly when they are in
the same `D` orbit.  Here we prove the corresponding universal property:

**every function invariant under the diagonal reversal factors uniquely through `χ`.**

Thus, if the simultaneous `(q,t) -> (-q,-t)` reversal is a genuine gauge/deck
identification, then no physical observable on the quotient can depend on the bare two
signs separately.  It can depend only on the two-valued relational class.

This is a finite exact theorem.  The physical hypothesis that the diagonal reversal is
indeed gauge/deck redundancy is separate.
-/

namespace GppOrientationQuotientUniversalProperty

open GppOrientationMassTime

/-- Canonical representative of a relational class: choose first sign `false`. -/
def quotientRep (c : Bool) : Bool × Bool := (false, c)

/-- The canonical representative has relational character exactly `c`. -/
theorem xorCharacter_quotientRep (c : Bool) :
    xorCharacter (quotientRep c) = c := by
  cases c <;> decide

/-- Every diagonal-invariant function factors through the relational character. -/
theorem invariant_factors_through_xor
    {α : Type*} (f : Bool × Bool → α)
    (hinv : ∀ x, f (diagFlip x) = f x) :
    ∃ g : Bool → α, ∀ x, f x = g (xorCharacter x) := by
  let g : Bool → α := fun c => f (quotientRep c)
  refine ⟨g, ?_⟩
  intro x
  rcases x with ⟨q,t⟩
  cases q <;> cases t
  · rfl
  · rfl
  · simpa [g, quotientRep, xorCharacter, diagFlip] using (hinv (false,true))
  · simpa [g, quotientRep, xorCharacter, diagFlip] using (hinv (false,false))

/-- Conversely, every function of the relational character is diagonal invariant. -/
theorem factors_through_xor_is_invariant
    {α : Type*} (g : Bool → α) :
    ∀ x, g (xorCharacter (diagFlip x)) = g (xorCharacter x) := by
  intro x
  rw [xorCharacter_diagFlip]

/-- Exact equivalence between diagonal invariance and factorization through `χ`. -/
theorem invariant_iff_factors_through_xor
    {α : Type*} (f : Bool × Bool → α) :
    (∀ x, f (diagFlip x) = f x) ↔
      ∃ g : Bool → α, ∀ x, f x = g (xorCharacter x) := by
  constructor
  · exact invariant_factors_through_xor f
  · rintro ⟨g,hg⟩ x
    rw [hg (diagFlip x), hg x, xorCharacter_diagFlip]

/-- The factor through `χ` is unique. -/
theorem xor_factor_unique
    {α : Type*} (f : Bool × Bool → α) (g h : Bool → α)
    (hg : ∀ x, f x = g (xorCharacter x))
    (hh : ∀ x, f x = h (xorCharacter x)) :
    g = h := by
  funext c
  have hgc := hg (quotientRep c)
  have hhc := hh (quotientRep c)
  rw [xorCharacter_quotientRep] at hgc hhc
  exact hgc.symm.trans hhc

/-- Universal-property package: an invariant observable has one and only one function on
    the two relational classes that represents it. -/
theorem quotient_universal_property
    {α : Type*} (f : Bool × Bool → α)
    (hinv : ∀ x, f (diagFlip x) = f x) :
    ∃! g : Bool → α, ∀ x, f x = g (xorCharacter x) := by
  obtain ⟨g,hg⟩ := invariant_factors_through_xor f hinv
  refine ⟨g,hg,?_⟩
  intro h hh
  exact xor_factor_unique f h g hh hg

end GppOrientationQuotientUniversalProperty
