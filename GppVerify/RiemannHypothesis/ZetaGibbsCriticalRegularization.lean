import GppVerify.RiemannHypothesis.ZetaGibbsFreeEnergy
import Mathlib.Tactic

/-!
# Zeta Gibbs critical regularization

On the honest Gibbs domain `beta > 1`, isolate the universal simple-pole factor by

  H(beta) = (beta - 1) Z(beta).

This file proves the exact logarithmic decomposition

  log Z(beta) = log H(beta) - log(beta - 1)

and the corresponding exact free-energy split.  It deliberately does not assert that
`H` has a finite nonzero limit at `beta -> 1+`; that analytic regularity is a separate
zeta-specific theorem still to be supplied before any critical asymptotic is promoted.
-/

namespace GppZetaGibbsCriticalRegularization

open GppZetaGibbsSummability
open GppZetaGibbsFisher
open GppZetaGibbsFreeEnergy

/-- Pole-removed partition coordinate. -/
noncomputable def regularizedPartition (beta : ℝ) : ℝ := (beta - 1) * Z beta

/-- The pole-removed partition coordinate is strictly positive on the Gibbs domain. -/
theorem regularizedPartition_pos {beta : ℝ} (hbeta : 1 < beta) :
    0 < regularizedPartition beta := by
  unfold regularizedPartition
  exact mul_pos (sub_pos.mpr hbeta) (Z_pos hbeta)

/-- Exact separation of the universal logarithmic singularity at `beta = 1`. -/
theorem logZ_eq_log_regularized_sub_log_distance
    {beta : ℝ} (hbeta : 1 < beta) :
    Real.log (Z beta) =
      Real.log (regularizedPartition beta) - Real.log (beta - 1) := by
  have hdist : beta - 1 ≠ 0 := (sub_pos.mpr hbeta).ne'
  have hZ : Z beta ≠ 0 := (Z_pos hbeta).ne'
  rw [regularizedPartition, Real.log_mul hdist hZ]
  ring

/-- The Helmholtz free energy splits exactly into a regularized part and the universal
`log(beta-1)/beta` singular coordinate. -/
theorem freeEnergy_eq_regularized_split
    {beta : ℝ} (hbeta : 1 < beta) :
    freeEnergy beta =
      -(Real.log (regularizedPartition beta)) / beta +
        Real.log (beta - 1) / beta := by
  have hbeta0 : beta ≠ 0 := by linarith
  unfold freeEnergy
  rw [logZ_eq_log_regularized_sub_log_distance hbeta]
  field_simp [hbeta0]
  ring

end GppZetaGibbsCriticalRegularization

#print axioms GppZetaGibbsCriticalRegularization.regularizedPartition_pos
#print axioms GppZetaGibbsCriticalRegularization.logZ_eq_log_regularized_sub_log_distance
#print axioms GppZetaGibbsCriticalRegularization.freeEnergy_eq_regularized_split
