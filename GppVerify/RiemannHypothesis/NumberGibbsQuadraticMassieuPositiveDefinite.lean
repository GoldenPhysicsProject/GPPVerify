import GppVerify.RiemannHypothesis.NumberGibbsQuadraticMassieuNondegeneracy
import GppVerify.RiemannHypothesis.WeightedVarianceInfiniteStrict
import Mathlib.Tactic

/-!
# Positive-definite Massieu/Fisher geometry of the confined number-Gibbs family

The determinant of the exact `(L,L^2)` covariance response is already strictly
positive for every real `β` and every `η > 0`.  To upgrade nonsingularity to the
Sylvester criterion for a positive-definite two-parameter thermodynamic metric,
we still need one strictly positive leading principal minor.  This file obtains
`fisherBB > 0` directly from the abstract countable strict-variance theorem and
the two fixed positive support points `n=0,1`.  The positive determinant then
forces `fisherEE > 0` as well.
-/

namespace GppNumberGibbsQuadraticMassieuPositiveDefinite

open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticConfinement
open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticMassieuHessian
open GppNumberGibbsQuadraticMassieuFisherIdentification
open GppNumberGibbsQuadraticMassieuNondegeneracy
open GppWeightedVarianceInfiniteStrict
open GppZetaGibbsSummability

/-- The inverse-temperature diagonal Massieu response is a strictly positive
normalized variance throughout the quadratically confined domain. -/
theorem fisherBB_pos (β : ℝ) {η : ℝ} (hη : 0 < η) :
    0 < fisherBB β η := by
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hz1 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 1) := by
    simpa using summable_gibbsWeight_mul_logEnergy htwo
  have hz2 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 2) :=
    summable_gibbsWeight_mul_logEnergy_sq htwo
  have hMpow : Summable (fun n : ℕ =>
      numberGibbsWeight β η n * numberLogEnergy n ^ 1) :=
    summable_numberGibbs_moment_of_quadratic β η 1 hη hz1
  have hM : Summable (fun n : ℕ =>
      numberGibbsWeight β η n * numberLogEnergy n) := by
    simpa using hMpow
  have hQ : Summable (fun n : ℕ =>
      numberGibbsWeight β η n * numberLogEnergy n ^ 2) :=
    summable_numberGibbs_moment_of_quadratic β η 2 hη hz2
  have hWpos : 0 < ∑' n : ℕ, numberGibbsWeight β η n := by
    simpa [Z] using Z_pos β hη
  have hx01 : numberLogEnergy 0 ≠ numberLogEnergy 1 :=
    first_three_numberLogEnergy_pairwise_distinct.1
  have hvar := normalized_weighted_variance_pos_tsum
    (numberGibbsWeight β η) numberLogEnergy
    (numberGibbsWeight_nonneg β η)
    (summable_numberGibbsWeight β hη)
    hM hQ hWpos
    (numberGibbsWeight_pos β η 0)
    (numberGibbsWeight_pos β η 1)
    hx01
  rw [fisherBB_eq_covariance]
  simpa [M1, M2, Z] using hvar

/-- The confinement diagonal Massieu response is also strictly positive.  This
follows from the already-certified positive covariance determinant together
with strict positivity of the leading diagonal entry. -/
theorem fisherEE_pos (β : ℝ) {η : ℝ} (hη : 0 < η) :
    0 < fisherEE β η := by
  have hbb : 0 < fisherBB β η := fisherBB_pos β hη
  have hdet := fisherBE_sq_lt_fisherBB_mul_fisherEE β hη
  nlinarith [sq_nonneg (fisherBE β η)]

/-- Sylvester package for the exact two-parameter Massieu/Fisher metric: both
diagonal variances and the determinant are strictly positive. -/
theorem massieuFisher_principal_minors_pos
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    0 < fisherBB β η ∧
      0 < massieuFisherDet β η ∧
      0 < fisherEE β η := by
  exact ⟨fisherBB_pos β hη, massieuFisherDet_pos β hη, fisherEE_pos β hη⟩

end GppNumberGibbsQuadraticMassieuPositiveDefinite

#print axioms GppNumberGibbsQuadraticMassieuPositiveDefinite.fisherBB_pos
#print axioms GppNumberGibbsQuadraticMassieuPositiveDefinite.fisherEE_pos
#print axioms GppNumberGibbsQuadraticMassieuPositiveDefinite.massieuFisher_principal_minors_pos
