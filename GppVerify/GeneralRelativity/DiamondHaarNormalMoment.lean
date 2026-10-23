import Mathlib.Tactic

/-!
# Isotropic boundary normal measure and unweighted York-volume response

For the standard rotation-invariant surface measure on the sphere
S^(n-1)_R, the normal second moment satisfies
  ∫_{∂B} nu_i nu_j dA = (A/n) delta_ij.
This follows from orthogonal invariance of the measure and the trace
identity ∑_i nu_i²=1. The group/measure-theoretic proof of this
identity is an explicit still-open library integration step; HERE the
second moment is represented by its isotropic tensor.

For an arbitrary constant (not necessarily isotropic) spatial metric
perturbation gamma_ij at the flat Euclidean ball, the bulk lapse
Hessian pairing is proportional to tr(gamma) and the boundary normal
integral cancels it exactly. The result uses only the isotropic
normal-second-moment identity and A=nV/R.

In particular the isotropic O(n) channel of the constant perturbation
is precisely the unweighted proper volume variation; traceless
anisotropy contributes neither net interior trace work nor net
boundary normal work.

This does NOT imply that Haar invariance forces fixing volume in the
physical ensemble. It identifies the measure responsible for the
*unweighted scalar variation*, not the boundary condition.
-/

namespace GppDiamondHaarNormalMoment

open scoped BigOperators

variable {n : ℕ}

/-- Linearized trace of an arbitrary constant metric perturbation. -/
def matrixTrace (gamma : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, gamma i i

/-- Pairing a constant symmetric tensor with the integrated normal
second-moment matrix (symmetry of gamma is not needed algebraically). -/
def normalMomentContraction
    (moment gamma : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, moment i j * gamma i j

/-- The unique O(n)-isotropic second-moment tensor with trace A. -/
noncomputable def isotropicNormalMoment (A : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => if i = j then A / (n : ℝ) else 0

theorem isotropic_normal_contraction
    (A : ℝ) (gamma : Fin n → Fin n → ℝ) :
    normalMomentContraction (isotropicNormalMoment (n := n) A) gamma =
      (A / (n : ℝ)) * matrixTrace gamma := by
  unfold normalMomentContraction isotropicNormalMoment matrixTrace
  calc
    (∑ i, ∑ j, (if i = j then A / (n : ℝ) else 0) * gamma i j) =
        ∑ i, (A / (n : ℝ)) * gamma i i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp
    _ = (A / (n : ℝ)) * ∑ i, gamma i i := by
          rw [Finset.mul_sum]

/-- The integral of the remaining boundary term when the CKV lapse
vanishes at the boundary and has outward normal derivative -1. -/
noncomputable def boundaryNormalWork (A : ℝ)
    (gamma : Fin n → Fin n → ℝ) : ℝ :=
  normalMomentContraction (isotropicNormalMoment (n := n) A) gamma -
    A * matrixTrace gamma

/-- The integrated interior trace-Hessian CKV term. -/
noncomputable def interiorTraceWork (R V : ℝ)
    (gamma : Fin n → Fin n → ℝ) : ℝ :=
  ((n : ℝ) - 1) / R * V * matrixTrace gamma

/-- The proper-volume differential in a constant spatial metric
perturbation at a Euclidean reference ball. -/
noncomputable def constantMetricVolumeResponse (V : ℝ)
    (gamma : Fin n → Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * V * matrixTrace gamma

/-- For EVERY constant tensor gamma, the isotropic sphere normal
moment makes the scalar-curvature bulk and boundary terms cancel. -/
theorem any_constant_metric_bulk_surface_cancel
    (R V A : ℝ) (gamma : Fin n → Fin n → ℝ)
    (hR : R ≠ 0) (hn : (n : ℝ) ≠ 0)
    (hAV : A = (n : ℝ) * V / R) :
    interiorTraceWork R V gamma +
      boundaryNormalWork A gamma = 0 := by
  unfold interiorTraceWork boundaryNormalWork
  rw [isotropic_normal_contraction, hAV]
  field_simp
  ring

/-- The bulk O(n)-invariant scalar channel is *exactly*
the unweighted proper-volume differential. -/
theorem interior_trace_is_york_volume
    (R V : ℝ) (gamma : Fin n → Fin n → ℝ) :
    interiorTraceWork R V gamma =
      (2 * ((n : ℝ) - 1) / R) *
        constantMetricVolumeResponse V gamma := by
  unfold interiorTraceWork constantMetricVolumeResponse
  ring

/-- Traceless anisotropic variations do not affect the interior
trace-Hessian work or the isotropic normal surface average. -/
theorem traceless_anisotropy_invisible_to_scalar_channel
    (R V A : ℝ) (gamma : Fin n → Fin n → ℝ)
    (htr : matrixTrace gamma = 0) :
    interiorTraceWork R V gamma = 0 ∧
    boundaryNormalWork A gamma = 0 ∧
    constantMetricVolumeResponse V gamma = 0 := by
  simp [interiorTraceWork, boundaryNormalWork,
    constantMetricVolumeResponse, isotropic_normal_contraction, htr]

end GppDiamondHaarNormalMoment

#print axioms GppDiamondHaarNormalMoment.isotropic_normal_contraction
#print axioms GppDiamondHaarNormalMoment.any_constant_metric_bulk_surface_cancel
#print axioms GppDiamondHaarNormalMoment.interior_trace_is_york_volume
#print axioms GppDiamondHaarNormalMoment.traceless_anisotropy_invisible_to_scalar_channel
