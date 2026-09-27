import GppVerify.RiemannHypothesis.NumberGibbsQuadraticMassieuHessian
import GppVerify.RiemannHypothesis.NumberGibbsQuadraticFisherGeometry
import Mathlib.Tactic

/-!
# Identification of the Massieu Hessian with Fisher geometry

The countable response calculation gives the three entries of the Hessian of `log Z`
as the covariance matrix of the sufficient statistics `L` and `L^2`.  The independent
Fisher-geometry development already proves strict positivity of the same normalized
covariance determinant.  This file identifies the two packages exactly and transfers
strict positivity to the Massieu Hessian determinant.
-/

namespace GppNumberGibbsQuadraticMassieuFisherIdentification

open GppFiniteFisherMomentBridge
open GppCountableFisherMomentLimit
open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticMassieuHessian
open GppNumberGibbsQuadraticFisherGeometry

/-- The first countable raw moment is exactly `M1`. -/
theorem infiniteMoment_one_eq_M1 (β η : ℝ) :
    infiniteMoment (numberGibbsWeight β η) numberLogEnergy 1 = M1 β η := by
  unfold infiniteMoment M1
  simp

/-- The second countable raw moment is exactly `M2`. -/
theorem infiniteMoment_two_eq_M2 (β η : ℝ) :
    infiniteMoment (numberGibbsWeight β η) numberLogEnergy 2 = M2 β η := by
  rfl

/-- The third countable raw moment is exactly `M3`. -/
theorem infiniteMoment_three_eq_M3 (β η : ℝ) :
    infiniteMoment (numberGibbsWeight β η) numberLogEnergy 3 = M3 β η := by
  rfl

/-- The fourth countable raw moment is exactly `M4`. -/
theorem infiniteMoment_four_eq_M4 (β η : ℝ) :
    infiniteMoment (numberGibbsWeight β η) numberLogEnergy 4 = M4 β η := by
  rfl

/-- Determinant of the exact Massieu/Fisher response matrix. -/
noncomputable def massieuFisherDet (β η : ℝ) : ℝ :=
  fisherBB β η * fisherEE β η - fisherBE β η ^ 2

/-- The determinant built from the exact Massieu response entries is precisely the
normalized Fisher covariance determinant of `L` and `L^2`. -/
theorem massieuFisherDet_eq_normalized_fisherDet (β η : ℝ) :
    massieuFisherDet β η =
      fisherDet (M1 β η / Z β η) (M2 β η / Z β η)
        (M3 β η / Z β η) (M4 β η / Z β η) := by
  by_cases hZ : Z β η = 0
  · simp [massieuFisherDet, fisherBB, fisherBE, fisherEE, fisherDet, hZ]
  · unfold massieuFisherDet fisherBB fisherBE fisherEE fisherDet
    field_simp [hZ]
    ring

/-- On the confined domain `η > 0`, the Massieu Hessian determinant is strictly
positive.  Hence the exact two-parameter fluctuation metric is positive definite. -/
theorem massieuFisherDet_pos
    (β : ℝ) {η : ℝ} (hη : 0 < η) : 0 < massieuFisherDet β η := by
  rw [massieuFisherDet_eq_normalized_fisherDet]
  have h := normalized_numberGibbs_fisherDet_pos β hη
  rw [infiniteMoment_zero_eq_Z,
    infiniteMoment_one_eq_M1,
    infiniteMoment_two_eq_M2,
    infiniteMoment_three_eq_M3,
    infiniteMoment_four_eq_M4] at h
  exact h

end GppNumberGibbsQuadraticMassieuFisherIdentification

#print axioms GppNumberGibbsQuadraticMassieuFisherIdentification.infiniteMoment_one_eq_M1
#print axioms GppNumberGibbsQuadraticMassieuFisherIdentification.massieuFisherDet_eq_normalized_fisherDet
#print axioms GppNumberGibbsQuadraticMassieuFisherIdentification.massieuFisherDet_pos
