import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import GppVerify.CelestialHolography.PenroseLocalTwistorRayGaugeCovariance

/-!
# Tautological spinor-line twist in the Penrose raywise quotient

The quotient coordinates `(x,p)` extracted from Penrose local-twistor transport satisfy
the same second-order Sturm equation as the null almost-Einstein scale.  However, they are
not themselves little-group invariant.

For a null factorization

  k = lambda * lambdatilde,

rescaling the spinor frame by

  lambda -> a lambda,
  lambdatilde -> a^{-1} lambdatilde

leaves the null direction fixed, while the quotient coordinates transform as

  (x,p) -> a^{-1}(x,p).

Thus the coordinate pair is naturally twisted by the tautological unprimed spinor line.
The frame-independent object is the tensor

  lambda tensor (x,p).

This module proves that finite algebra exactly and also records a concrete obstruction to
identifying the raw coordinate `x` with an ordinary little-group-neutral scalar.

Geometric consequence: the projectivized quotient agrees canonically with the raywise
projective/Sturm geometry, but any vector-bundle comparison with a scalar Einstein-scale
bundle must account for this tautological line twist (or an equivalent spin/theta choice).
No claim about the exact holomorphic line-bundle notation on curved ambitwistor space is
made here.
-/

namespace GppPenroseQuotientTautologicalTwist

open Complex
open GppPenroseLocalTwistorEinsteinQuotient
open GppPenroseLocalTwistorRayGaugeCovariance

abbrev CSpinor2 := ℂ × ℂ

/-- Scale a complex two-spinor. -/
def scaleCSpinor (a : ℂ) (lambda : CSpinor2) : CSpinor2 :=
  (a*lambda.1,a*lambda.2)

/-- Concrete four-coordinate carrier for `lambda tensor u`, with `u=(x,p)`. -/
def spinorStateTensor (lambda : CSpinor2) (u : EinsteinRayState) :
    ℂ × ℂ × ℂ × ℂ :=
  (lambda.1*u.1,
   lambda.1*u.2,
   lambda.2*u.1,
   lambda.2*u.2)

/-- Opposite scalings of the spinor frame and quotient coordinates cancel exactly in the
tensor product. -/
theorem spinorStateTensor_biscaling
    (a c : ℂ) (lambda : CSpinor2) (u : EinsteinRayState) :
    spinorStateTensor (scaleCSpinor a lambda) (scaleEinsteinState c u) =
      let ac := a*c
      (ac*(lambda.1*u.1),
       ac*(lambda.1*u.2),
       ac*(lambda.2*u.1),
       ac*(lambda.2*u.2)) := by
  rcases lambda with ⟨l0,l1⟩
  rcases u with ⟨x,p⟩
  simp [spinorStateTensor, scaleCSpinor, scaleEinsteinState]
  apply Prod.ext
  · ring
  · apply Prod.ext
    · ring
    · apply Prod.ext <;> ring

/-- Main twist-cancellation theorem: under the null-spinor little group, the tensor is
strictly invariant. -/
theorem spinorStateTensor_littleGroup_invariant
    (a : ℂ) (ha : a ≠ 0)
    (lambda : CSpinor2) (u : EinsteinRayState) :
    spinorStateTensor (scaleCSpinor a lambda) (littleGroupState a ha u) =
      spinorStateTensor lambda u := by
  rw [littleGroupState]
  rw [spinorStateTensor_biscaling]
  have hai : a * a⁻¹ = 1 := by exact mul_inv_cancel₀ ha
  simp [hai, spinorStateTensor]

/-- The aligned primary spinor `omega = x lambda` is itself little-group invariant. -/
def alignedPrimary (lambda : CSpinor2) (u : EinsteinRayState) : CSpinor2 :=
  (u.1*lambda.1,u.1*lambda.2)

/-- Gauge invariance of the aligned primary spinor. -/
theorem alignedPrimary_littleGroup_invariant
    (a : ℂ) (ha : a ≠ 0)
    (lambda : CSpinor2) (u : EinsteinRayState) :
    alignedPrimary (scaleCSpinor a lambda) (littleGroupState a ha u) =
      alignedPrimary lambda u := by
  rcases lambda with ⟨l0,l1⟩
  rcases u with ⟨x,p⟩
  simp [alignedPrimary, scaleCSpinor, littleGroupState, scaleEinsteinState]
  have hai : a⁻¹ * a = 1 := inv_mul_cancel₀ ha
  apply Prod.ext <;> simp [hai] <;> ring

/-- Concrete obstruction: the raw first quotient coordinate is not little-group invariant.
For the state `(1,0)`, rescaling the spinor frame by `2` changes it to `1/2`. -/
theorem raw_x_coordinate_not_gauge_invariant :
    (littleGroupState (2 : ℂ) (by norm_num) ((1 : ℂ),(0 : ℂ))).1 ≠ 1 := by
  norm_num [littleGroupState, scaleEinsteinState]

/-- The projective content survives the twist: little-group change is a common nonzero
scalar on the two-component quotient state. -/
theorem littleGroup_is_common_nonzero_scale
    (a : ℂ) (ha : a ≠ 0) (u : EinsteinRayState) :
    littleGroupState a ha u = scaleEinsteinState (a⁻¹) u ∧ a⁻¹ ≠ 0 := by
  exact ⟨rfl, inv_ne_zero ha⟩

end GppPenroseQuotientTautologicalTwist
