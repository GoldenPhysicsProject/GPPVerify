import Mathlib.Tactic
import GppVerify.CelestialHolography.TwistorCanonicalShift

/-!
# Projective Fourier transform modulo Penrose-null ambiguity

For homogeneous twistor data the full four-dimensional Fourier transform is naturally
distributional.  Its projective formula may depend on a choice of scale/regularization;
for nonnegative target homogeneity the ambiguity is a homogeneous polynomial which is
annihilated by the corresponding Penrose/X-ray transform.

This module formalizes the quotient logic only.  It does not prove the analytic
projective Fourier integral.  The point is that once two regularizations differ by a
Penrose-null term, they define exactly the same bulk field, so the field-level transform
is well-defined on the quotient even when a representative is not unique.
-/

namespace GppProjectiveFourierPenroseQuotient

open GppTwistorCanonicalShift
open GppTwistorWeightDuality

variable {K Tw Dual Bulk : Type*}
  [Field K]
  [AddCommGroup Dual] [Module K Dual]
  [AddCommGroup Bulk] [Module K Bulk]

/-- Two dual-twistor representatives are physically/Penrose equivalent when they have
the same bulk image. -/
def PenroseEquivalent (P : Dual →ₗ[K] Bulk) (f g : Dual) : Prop :=
  P f = P g

/-- Adding any Penrose-null ambiguity leaves the reconstructed bulk field unchanged. -/
theorem add_kernel_same_penrose
    (P : Dual →ₗ[K] Bulk) (f q : Dual) (hq : P q = 0) :
    P (f + q) = P f := by
  rw [map_add, hq, add_zero]

/-- Consequently `f` and `f+q` are equivalent whenever `q` lies in the Penrose kernel. -/
theorem add_kernel_penroseEquivalent
    (P : Dual →ₗ[K] Bulk) (f q : Dual) (hq : P q = 0) :
    PenroseEquivalent P (f + q) f :=
  add_kernel_same_penrose P f q hq

/-- If two regularized/projective Fourier representatives differ by a Penrose-null
term, the ambiguity disappears exactly after bulk reconstruction. -/
theorem regularization_independent_on_bulk
    (P : Dual →ₗ[K] Bulk) (f₁ f₂ q : Dual)
    (hrel : f₂ = f₁ + q) (hq : P q = 0) :
    P f₂ = P f₁ := by
  rw [hrel]
  exact add_kernel_same_penrose P f₁ q hq

/-- The corresponding quotient relation is reflexive. -/
theorem penroseEquivalent_refl (P : Dual →ₗ[K] Bulk) (f : Dual) :
    PenroseEquivalent P f f := rfl

/-- It is symmetric. -/
theorem penroseEquivalent_symm
    (P : Dual →ₗ[K] Bulk) {f g : Dual}
    (h : PenroseEquivalent P f g) : PenroseEquivalent P g f :=
  h.symm

/-- And transitive. -/
theorem penroseEquivalent_trans
    (P : Dual →ₗ[K] Bulk) {f g h : Dual}
    (hfg : PenroseEquivalent P f g) (hgh : PenroseEquivalent P g h) :
    PenroseEquivalent P f h :=
  hfg.trans hgh

/-! ## Homogeneity bookkeeping

The projective Fourier transform in ambient rank four pairs source degree `-n-4`
with target degree `n`.  This is exactly the canonical-bundle reflection already
formalized elsewhere.
-/

/-- Source degree for a target homogeneous degree `n`. -/
def projectiveFourierSourceWeight (n : ℤ) : ℤ := -n - 4

/-- The source/target projective Fourier weights are exactly related by the ambient
rank-four canonical reflection. -/
theorem sourceWeight_eq_serreWeight (n : ℤ) :
    projectiveFourierSourceWeight n = serreWeight n := by
  norm_num [projectiveFourierSourceWeight, serreWeight, canonicalDegree,
    projectiveTwistorDim]

/-- Applying the canonical reflection to the source returns the target degree. -/
theorem sourceWeight_reflects_to_target (n : ℤ) :
    serreWeight (projectiveFourierSourceWeight n) = n := by
  rw [sourceWeight_eq_serreWeight]
  exact serreWeight_involutive n

/-- For a graviton target of weight `+2`, the source is weight `-6`. -/
theorem graviton_projective_fourier_pair :
    projectiveFourierSourceWeight 2 = -6 ∧ serreWeight (-6) = 2 := by
  norm_num [projectiveFourierSourceWeight, serreWeight, canonicalDegree,
    projectiveTwistorDim]

/-- Conversely a target of weight `-6` has source weight `+2`. -/
theorem opposite_graviton_projective_fourier_pair :
    projectiveFourierSourceWeight (-6) = 2 ∧ serreWeight 2 = -6 := by
  norm_num [projectiveFourierSourceWeight, serreWeight, canonicalDegree,
    projectiveTwistorDim]

end GppProjectiveFourierPenroseQuotient
