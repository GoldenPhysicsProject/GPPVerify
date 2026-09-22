import Mathlib.Tactic
import GppVerify.CelestialHolography.PenroseQuotientDescent

/-!
# Projective googly involution on Penrose classes

Representative-level projective Fourier transforms can carry regularization or
polynomial ambiguity.  The physical statement should therefore be made on Penrose
classes.  This module proves a useful closure theorem: if forward and backward
representative transforms intertwine the two Penrose maps with mutually inverse bulk
operations, then their descended maps are mutually inverse on the Penrose quotients.

Crucially, no representative-level identity `G(F a)=a` is required.  Any discrepancy
lying in the Penrose kernel disappears automatically in the quotient.
-/

namespace GppProjectiveGooglyInvolution

open GppPenroseQuotientDescent

variable {K A B BulkA BulkB : Type*}
  [Field K]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]
  [AddCommGroup BulkA] [Module K BulkA]
  [AddCommGroup BulkB] [Module K BulkB]

structure TwoSidedPenroseIntertwiner
    (PA : A →ₗ[K] BulkA) (PB : B →ₗ[K] BulkB) where
  forward : A → B
  backward : B → A
  bulkForward : BulkA → BulkB
  bulkBackward : BulkB → BulkA
  forward_intertwines : ∀ a, PB (forward a) = bulkForward (PA a)
  backward_intertwines : ∀ b, PA (backward b) = bulkBackward (PB b)
  bulk_left_inverse : ∀ x, bulkBackward (bulkForward x) = x
  bulk_right_inverse : ∀ y, bulkForward (bulkBackward y) = y

/-- The forward representative transform respects Penrose equivalence. -/
theorem forward_respects
    (PA : A →ₗ[K] BulkA) (PB : B →ₗ[K] BulkB)
    (G : TwoSidedPenroseIntertwiner PA PB) :
    RespectsPenrose PA PB G.forward :=
  respectsPenrose_of_intertwiner PA PB G.forward G.bulkForward G.forward_intertwines

/-- The backward representative transform respects Penrose equivalence. -/
theorem backward_respects
    (PA : A →ₗ[K] BulkA) (PB : B →ₗ[K] BulkB)
    (G : TwoSidedPenroseIntertwiner PA PB) :
    RespectsPenrose PB PA G.backward :=
  respectsPenrose_of_intertwiner PB PA G.backward G.bulkBackward G.backward_intertwines

/-- Forward then backward is the identity on physical/Penrose classes even when it
need not be literally the identity on representatives. -/
theorem descended_backward_forward
    (PA : A →ₗ[K] BulkA) (PB : B →ₗ[K] BulkB)
    (G : TwoSidedPenroseIntertwiner PA PB) :
    (descend PB PA G.backward (backward_respects PA PB G)) ∘
      (descend PA PB G.forward (forward_respects PA PB G)) = id := by
  funext q
  apply bulkOfClass_injective PA
  induction q using Quotient.inductionOn with
  | _ a =>
      simp [Function.comp_def, G.backward_intertwines,
        G.forward_intertwines, G.bulk_left_inverse]

/-- Backward then forward is likewise the identity on the dual Penrose quotient. -/
theorem descended_forward_backward
    (PA : A →ₗ[K] BulkA) (PB : B →ₗ[K] BulkB)
    (G : TwoSidedPenroseIntertwiner PA PB) :
    (descend PA PB G.forward (forward_respects PA PB G)) ∘
      (descend PB PA G.backward (backward_respects PA PB G)) = id := by
  funext q
  apply bulkOfClass_injective PB
  induction q using Quotient.inductionOn with
  | _ b =>
      simp [Function.comp_def, G.forward_intertwines,
        G.backward_intertwines, G.bulk_right_inverse]

/-- Therefore the two descended googly maps are a genuine equivalence between the two
spaces of physical Penrose classes. -/
theorem descended_bijection
    (PA : A →ₗ[K] BulkA) (PB : B →ₗ[K] BulkB)
    (G : TwoSidedPenroseIntertwiner PA PB) :
    Function.Bijective (descend PA PB G.forward (forward_respects PA PB G)) := by
  constructor
  · intro x y hxy
    have h := congrArg
      (descend PB PA G.backward (backward_respects PA PB G)) hxy
    have hleft := congrFun (descended_backward_forward PA PB G) x
    have hright := congrFun (descended_backward_forward PA PB G) y
    simpa [Function.comp_def, hleft, hright] using h
  · intro y
    refine ⟨descend PB PA G.backward (backward_respects PA PB G) y, ?_⟩
    have h := congrFun (descended_forward_backward PA PB G) y
    simpa [Function.comp_def] using h

end GppProjectiveGooglyInvolution
