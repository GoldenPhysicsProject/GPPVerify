import GppVerify.RiemannHypothesis.NumberGibbsQuadraticThermodynamics
import Mathlib.Tactic

/-!
# Normalized Fisher geometry for the quadratically confined number-Gibbs family

The quadratic-confinement theorem gives strict positivity of the division-free
Fisher numerator for the sufficient statistics `L` and `L^2`.  Since the
partition mass is strictly positive, probability normalization preserves
strict positivity.  This file packages that exact bridge without invoking any
differentiability of the partition function.
-/

namespace GppNumberGibbsQuadraticFisherGeometry

open GppFiniteFisherMomentBridge
open GppCountableFisherMomentLimit
open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticConfinement
open GppNumberGibbsQuadraticThermodynamics

/-- Probability normalization divides the mass-aware Fisher numerator by the
fourth power of the total mass. -/
theorem normalized_fisherDet_eq_fisherNumerator_div_mass_four
    (m0 m1 m2 m3 m4 : ℝ) (hm0 : m0 ≠ 0) :
    fisherDet (m1 / m0) (m2 / m0) (m3 / m0) (m4 / m0) =
      fisherNumerator m0 m1 m2 m3 m4 / m0 ^ 4 := by
  unfold fisherDet fisherNumerator
  field_simp [hm0]

/-- The zeroth raw moment is exactly the thermodynamic partition function. -/
theorem infiniteMoment_zero_eq_Z (β η : ℝ) :
    infiniteMoment (numberGibbsWeight β η) numberLogEnergy 0 = Z β η := by
  unfold infiniteMoment Z
  simp

/-- The normalized covariance determinant of `L` and `L^2` for the
quadratically confined number-Gibbs probability law is strictly positive for
every real `β` and every `η > 0`. -/
theorem normalized_numberGibbs_fisherDet_pos
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    0 < fisherDet
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 1 /
        infiniteMoment (numberGibbsWeight β η) numberLogEnergy 0)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 2 /
        infiniteMoment (numberGibbsWeight β η) numberLogEnergy 0)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 3 /
        infiniteMoment (numberGibbsWeight β η) numberLogEnergy 0)
      (infiniteMoment (numberGibbsWeight β η) numberLogEnergy 4 /
        infiniteMoment (numberGibbsWeight β η) numberLogEnergy 0) := by
  let w : ℕ → ℝ := numberGibbsWeight β η
  let x : ℕ → ℝ := numberLogEnergy
  let m0 : ℝ := infiniteMoment w x 0
  let m1 : ℝ := infiniteMoment w x 1
  let m2 : ℝ := infiniteMoment w x 2
  let m3 : ℝ := infiniteMoment w x 3
  let m4 : ℝ := infiniteMoment w x 4
  have hm0 : 0 < m0 := by
    dsimp [m0, w, x]
    rw [infiniteMoment_zero_eq_Z]
    exact Z_pos β hη
  have hnum : 0 < fisherNumerator m0 m1 m2 m3 m4 := by
    dsimp [m0, m1, m2, m3, m4, w, x]
    exact numberGibbs_fisherNumerator_infinite_pos_of_eta_pos β hη
  have hnorm := normalized_fisherDet_eq_fisherNumerator_div_mass_four
    m0 m1 m2 m3 m4 (ne_of_gt hm0)
  rw [hnorm]
  exact div_pos hnum (pow_pos hm0 4)

end GppNumberGibbsQuadraticFisherGeometry

#print axioms GppNumberGibbsQuadraticFisherGeometry.normalized_fisherDet_eq_fisherNumerator_div_mass_four
#print axioms GppNumberGibbsQuadraticFisherGeometry.infiniteMoment_zero_eq_Z
#print axioms GppNumberGibbsQuadraticFisherGeometry.normalized_numberGibbs_fisherDet_pos
