import GppVerify.RiemannHypothesis.NumberGibbsQuadraticMassieuFisherIdentification
import Mathlib.Tactic

/-!
# Strict nondegeneracy of the quadratic number-Gibbs Massieu response

The previous module identifies the exact Hessian determinant of `log Z` with
the normalized Fisher covariance determinant and proves it is strictly positive
for every real `β` and every confining parameter `η > 0`.  This file records the
immediate strict covariance inequality and nonsingularity consequences in the
Massieu notation used by the thermodynamic front.
-/

namespace GppNumberGibbsQuadraticMassieuNondegeneracy

open GppNumberGibbsQuadraticMassieuHessian
open GppNumberGibbsQuadraticMassieuFisherIdentification

/-- The exact covariance entries satisfy the strict determinant inequality on
the confined domain. -/
theorem fisherBE_sq_lt_fisherBB_mul_fisherEE
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    fisherBE β η ^ 2 < fisherBB β η * fisherEE β η := by
  have h := massieuFisherDet_pos β hη
  unfold massieuFisherDet at h
  linarith

/-- The exact Massieu/Fisher Hessian determinant never vanishes for `η > 0`. -/
theorem massieuFisherDet_ne_zero
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    massieuFisherDet β η ≠ 0 :=
  ne_of_gt (massieuFisherDet_pos β hη)

end GppNumberGibbsQuadraticMassieuNondegeneracy

#print axioms GppNumberGibbsQuadraticMassieuNondegeneracy.fisherBE_sq_lt_fisherBB_mul_fisherEE
#print axioms GppNumberGibbsQuadraticMassieuNondegeneracy.massieuFisherDet_ne_zero
