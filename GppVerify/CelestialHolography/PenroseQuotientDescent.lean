import Mathlib.Tactic
import GppVerify.CelestialHolography.ProjectiveFourierPenroseQuotient

/-!
# Penrose quotient descent for projective Fourier duality

A projective/distributional Fourier representative can be non-unique while its Penrose
image is unique.  The correct field-level object is therefore the quotient by equality
of Penrose image.  This file constructs that quotient explicitly and proves the precise
criterion under which a twistor transform descends to it.

No analytic Fourier theorem is assumed here.  The result isolates the remaining task:
prove that the concrete projective Fourier/Radon transform respects Penrose equivalence.
-/

namespace GppPenroseQuotientDescent

variable {K A B BulkA BulkB : Type*}
  [Field K]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]
  [AddCommGroup BulkA] [Module K BulkA]
  [AddCommGroup BulkB] [Module K BulkB]

/-- Equality after a linear Penrose map is an equivalence relation. -/
def penroseSetoid (P : A →ₗ[K] BulkA) : Setoid A where
  r x y := P x = P y
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }

/-- Twistor representatives modulo Penrose-null ambiguity. -/
abbrev PenroseQuotient (P : A →ₗ[K] BulkA) := Quotient (penroseSetoid P)

/-- Bulk reconstruction is well-defined on Penrose equivalence classes. -/
def bulkOfClass (P : A →ₗ[K] BulkA) : PenroseQuotient P → BulkA :=
  Quotient.lift P (by
    intro a b hab
    exact hab)

@[simp] theorem bulkOfClass_mk (P : A →ₗ[K] BulkA) (a : A) :
    bulkOfClass P (Quotient.mk' a) = P a := rfl

/-- The quotient removes exactly and only Penrose-invisible ambiguity: the induced
bulk map is injective. -/
theorem bulkOfClass_injective (P : A →ₗ[K] BulkA) :
    Function.Injective (bulkOfClass P) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
          apply Quotient.sound
          exact hxy

/-- A transform respects physical/Penrose equivalence when equal source bulk fields
are sent to equal target bulk fields. -/
def RespectsPenrose
    (PA : A →ₗ[K] BulkA) (PB : B →ₗ[K] BulkB) (F : A → B) : Prop :=
  ∀ ⦃a₁ a₂ : A⦄, PA a₁ = PA a₂ → PB (F a₁) = PB (F a₂)

/-- Any transform respecting Penrose equivalence descends canonically to the quotient. -/
def descend
    (PA : A →ₗ[K] BulkA) (PB : B →ₗ[K] BulkB) (F : A → B)
    (hF : RespectsPenrose PA PB F) :
    PenroseQuotient PA → PenroseQuotient PB :=
  Quotient.map F (by
    intro a₁ a₂ h
    exact hF h)

@[simp] theorem descend_mk
    (PA : A →ₗ[K] BulkA) (PB : B →ₗ[K] BulkB) (F : A → B)
    (hF : RespectsPenrose PA PB F) (a : A) :
    descend PA PB F hF (Quotient.mk' a) = Quotient.mk' (F a) := rfl

/-- If the transform intertwines the Penrose maps through a bulk map `R`, then it
automatically respects Penrose equivalence and hence descends to physical classes. -/
theorem respectsPenrose_of_intertwiner
    (PA : A →ₗ[K] BulkA) (PB : B →ₗ[K] BulkB)
    (F : A → B) (R : BulkA → BulkB)
    (hinter : ∀ a, PB (F a) = R (PA a)) :
    RespectsPenrose PA PB F := by
  intro a₁ a₂ h
  rw [hinter, hinter, h]

/-- The desired googly/Penrose commuting square therefore has a canonical quotient
version: once `PB(F a)=R(PA a)` is proved on representatives, the class map is
well-defined and its reconstructed bulk field is exactly `R(PA a)`. -/
theorem descended_intertwiner
    (PA : A →ₗ[K] BulkA) (PB : B →ₗ[K] BulkB)
    (F : A → B) (R : BulkA → BulkB)
    (hinter : ∀ a, PB (F a) = R (PA a)) (a : A) :
    bulkOfClass PB
      (descend PA PB F (respectsPenrose_of_intertwiner PA PB F R hinter)
        (Quotient.mk' a))
      = R (PA a) := by
  simp [hinter]

/-- Two representative-level transforms that differ only by target Penrose-null data
induce the same quotient transform. -/
theorem descended_maps_equal_of_same_penrose
    (PA : A →ₗ[K] BulkA) (PB : B →ₗ[K] BulkB)
    (F G : A → B)
    (hF : RespectsPenrose PA PB F)
    (hG : RespectsPenrose PA PB G)
    (hFG : ∀ a, PB (F a) = PB (G a)) :
    descend PA PB F hF = descend PA PB G hG := by
  funext q
  induction q using Quotient.inductionOn with
  | _ a =>
      apply Quotient.sound
      exact hFG a

end GppPenroseQuotientDescent
