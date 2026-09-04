import Mathlib.Tactic
import GppVerify.CelestialHolography.ProjectiveFourierPenroseQuotient

/-!
# Projective Fourier/Penrose intertwiner criterion

The finite-dimensional incidence and homogeneity calculations identify the candidate
googly operation.  The remaining analytic statement is a commuting square between a
projective Fourier transform and the two Penrose/X-ray reconstructions.

This file isolates the exact consequences of that square on physical field classes.
In particular, no injectivity of a representative-level Penrose map is needed to get
a well-defined transform on the quotient: the commuting square itself guarantees that
Penrose-equivalent source representatives are sent to Penrose-equivalent target
representatives.  A two-sided square closes after two transforms modulo the Penrose
kernel whenever bulk orientation reversal is involutive.

The analytic commuting square is a field of the structure below, not a theorem proved
here.  Thus this module records the precise remaining hypothesis without hiding it.
-/

namespace GppProjectiveFourierIntertwinerCriterion

variable {K Tw Dual Bulk : Type*}
  [Field K]
  [AddCommGroup Tw] [Module K Tw]
  [AddCommGroup Dual] [Module K Dual]
  [AddCommGroup Bulk] [Module K Bulk]

/-- A representative-level Fourier/Penrose commuting square. -/
structure PenroseFourierBridge where
  fourier : Tw →ₗ[K] Dual
  penroseSource : Tw →ₗ[K] Bulk
  penroseDual : Dual →ₗ[K] Bulk
  reverse : Bulk →ₗ[K] Bulk
  intertwines : ∀ z, penroseDual (fourier z) = reverse (penroseSource z)

namespace PenroseFourierBridge

variable (G : PenroseFourierBridge (K:=K) (Tw:=Tw) (Dual:=Dual) (Bulk:=Bulk))

/-- Physical equivalence on source representatives. -/
def SourceEquivalent (x y : Tw) : Prop :=
  G.penroseSource x = G.penroseSource y

/-- Physical equivalence on target representatives. -/
def TargetEquivalent (x y : Dual) : Prop :=
  G.penroseDual x = G.penroseDual y

/-- The commuting square automatically sends the source Penrose kernel into the target
Penrose kernel.  This is the exact condition required for quotient descent. -/
theorem maps_source_kernel_to_target_kernel
    (z : Tw) (hz : G.penroseSource z = 0) :
    G.penroseDual (G.fourier z) = 0 := by
  rw [G.intertwines, hz, map_zero]

/-- Consequently the representative-level Fourier transform is well-defined on
physical/Penrose equivalence classes. -/
theorem preserves_physical_equivalence
    {x y : Tw} (hxy : G.SourceEquivalent x y) :
    G.TargetEquivalent (G.fourier x) (G.fourier y) := by
  calc
    G.penroseDual (G.fourier x) = G.reverse (G.penroseSource x) := G.intertwines x
    _ = G.reverse (G.penroseSource y) := by rw [hxy]
    _ = G.penroseDual (G.fourier y) := (G.intertwines y).symm

/-- Adding a target Penrose-null regularization term does not alter the bulk field
produced by the Fourier/Penrose square. -/
theorem target_regularization_independent
    (z : Tw) (q : Dual) (hq : G.penroseDual q = 0) :
    G.penroseDual (G.fourier z + q) = G.reverse (G.penroseSource z) := by
  rw [map_add, hq, add_zero]
  exact G.intertwines z

end PenroseFourierBridge

/-- A two-sided representative-level bridge.  The forward and backward transforms may
fail to be literal inverses on representatives; physical closure follows from the two
commuting squares and involutivity of bulk orientation reversal. -/
structure TwoSidedPenroseFourierBridge where
  forward : Tw →ₗ[K] Dual
  backward : Dual →ₗ[K] Tw
  penroseSource : Tw →ₗ[K] Bulk
  penroseDual : Dual →ₗ[K] Bulk
  reverse : Bulk →ₗ[K] Bulk
  forward_intertwines : ∀ z,
    penroseDual (forward z) = reverse (penroseSource z)
  backward_intertwines : ∀ w,
    penroseSource (backward w) = reverse (penroseDual w)
  reverse_involutive : ∀ b, reverse (reverse b) = b

namespace TwoSidedPenroseFourierBridge

variable (G : TwoSidedPenroseFourierBridge (K:=K) (Tw:=Tw) (Dual:=Dual) (Bulk:=Bulk))

/-- Two transforms close exactly on the reconstructed bulk field, even if they do not
close on a chosen twistor representative. -/
theorem backward_forward_bulk_closure (z : Tw) :
    G.penroseSource (G.backward (G.forward z)) = G.penroseSource z := by
  rw [G.backward_intertwines, G.forward_intertwines]
  exact G.reverse_involutive (G.penroseSource z)

/-- The reverse order closes on the dual reconstructed bulk field. -/
theorem forward_backward_bulk_closure (w : Dual) :
    G.penroseDual (G.forward (G.backward w)) = G.penroseDual w := by
  rw [G.forward_intertwines, G.backward_intertwines]
  exact G.reverse_involutive (G.penroseDual w)

/-- Thus `backward ∘ forward` is the identity on physical source classes. -/
theorem backward_forward_physical_equivalent (z : Tw) :
    G.penroseSource (G.backward (G.forward z)) = G.penroseSource z :=
  G.backward_forward_bulk_closure z

/-- And `forward ∘ backward` is the identity on physical target classes. -/
theorem forward_backward_physical_equivalent (w : Dual) :
    G.penroseDual (G.forward (G.backward w)) = G.penroseDual w :=
  G.forward_backward_bulk_closure w

end TwoSidedPenroseFourierBridge

end GppProjectiveFourierIntertwinerCriterion
