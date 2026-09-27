import Mathlib.Tactic

/-!
# Abstract transport of Shadow structure

The Shadow framework repeatedly realizes one involution in different coordinates.
The correct invariant statement is conjugacy: if an equivalence `U : X ≃ Y`
intertwines two Shadow maps, then fixed points, involutivity, commuting operators,
and transported positivity are preserved.

This module isolates that reusable mathematical skeleton independently of any
particular Grassmannian, Mellin, celestial, or arithmetic realization.
-/

namespace GppShadowTransport

variable {X Y : Type*}

/-- A point is fixed by a specified Shadow map. -/
def FixedBy (sh : X → X) (x : X) : Prop := sh x = x

/-- Conjugate Shadow maps have exactly corresponding fixed points. -/
theorem fixedBy_iff_of_intertwines
    (U : X ≃ Y) (shX : X → X) (shY : Y → Y)
    (hsh : ∀ x, U (shX x) = shY (U x)) (x : X) :
    FixedBy shX x ↔ FixedBy shY (U x) := by
  constructor
  · intro hx
    unfold FixedBy at hx ⊢
    rw [← hsh x, hx]
  · intro hy
    unfold FixedBy at hy ⊢
    apply U.injective
    rw [hsh x, hy]

/-- Involutivity transports across a conjugating equivalence. -/
theorem involutive_of_intertwines
    (U : X ≃ Y) (shX : X → X) (shY : Y → Y)
    (hsh : ∀ x, U (shX x) = shY (U x))
    (hInvX : Function.Involutive shX) :
    Function.Involutive shY := by
  intro y
  obtain ⟨x, rfl⟩ := U.surjective y
  rw [← hsh, ← hsh, hInvX]

/-- Commutation with Shadow is invariant under simultaneous transport of the
Shadow map and an operator. -/
theorem commutes_with_shadow_of_intertwines
    (U : X ≃ Y) (shX A : X → X) (shY B : Y → Y)
    (hsh : ∀ x, U (shX x) = shY (U x))
    (hA : ∀ x, U (A x) = B (U x))
    (hcomm : Function.Commute shX A) :
    Function.Commute shY B := by
  intro y
  obtain ⟨x, rfl⟩ := U.surjective y
  rw [← hA, ← hsh, ← hsh, ← hA, hcomm.eq]

/-- Positivity of a real-valued quadratic/form functional is preserved by an
exactly transported functional.  The theorem is intentionally abstract: later
Hilbert-space realizations only need to prove the transport identity. -/
theorem nonnegative_iff_of_transport
    (U : X ≃ Y) (QX : X → ℝ) (QY : Y → ℝ)
    (hQ : ∀ x, QY (U x) = QX x) :
    (∀ x, 0 ≤ QX x) ↔ ∀ y, 0 ≤ QY y := by
  constructor
  · intro hX y
    obtain ⟨x, rfl⟩ := U.surjective y
    rw [hQ]
    exact hX x
  · intro hY x
    rw [← hQ]
    exact hY (U x)

end GppShadowTransport

#print axioms GppShadowTransport.fixedBy_iff_of_intertwines
#print axioms GppShadowTransport.involutive_of_intertwines
#print axioms GppShadowTransport.commutes_with_shadow_of_intertwines
#print axioms GppShadowTransport.nonnegative_iff_of_transport
