import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import GppVerify.GeneralRelativity.YorkVolumeSymplectic

/-!
# Gravitational time reversal, Schmidt entropy and variable spatial volume

A concrete answer to the observation that gravity has the same
time-reversal-even constraint in both microscopic time orientations.

* In an orthonormal spatial frame, the ADM scalar constraint depends on
  the extrinsic curvature only through K² and K_ij K^ij; it is invariant
  under the simultaneous reversal K_ij -> -K_ij.
* For a spinless/factorized antiunitary time reversal given by complex
  conjugation on Schmidt coefficients, reduced-state entropy is unchanged.
* The canonical symplectic form changes sign, as established separately
  in YorkVolumeSymplectic.
* Crucially, a time-reversal Z2 quotient does NOT make volume constant:
  different radii/volumes persist as distinct orbits. Thus time-reversal
  symmetry and entanglement-spectrum invariance alone cannot force the
  proper-volume constraint.

This does not identify the user's proposed microscopic t with Wigner
time reversal, nor claim gravity is always attractive in every spacetime.
-/

namespace GppTimeReversalVolume

open scoped BigOperators

section ADM

variable {n : ℕ}

/-- Trace of extrinsic curvature in an orthonormal spatial frame. -/
def traceK (K : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, K i i

/-- Pointwise Euclidean-frame contraction K_ij K^ij. -/
def squareK (K : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (K i j)^2

/-- Time-even ADM Hamiltonian constraint residual, in units 16πG=1. -/
noncomputable def hConstraint (spatialR energy cosmological : ℝ)
    (K : Fin n → Fin n → ℝ) : ℝ :=
  spatialR + (traceK K)^2 - squareK K - energy - 2 * cosmological

theorem traceK_time_odd (K : Fin n → Fin n → ℝ) :
    traceK (fun i j => -K i j) = -traceK K := by
  simp [traceK, Finset.sum_neg_distrib]

theorem squareK_time_even (K : Fin n → Fin n → ℝ) :
    squareK (fun i j => -K i j) = squareK K := by
  simp [squareK]

/-- The Hamiltonian constraint does not distinguish future from past
extrinsic-curvature orientation, with fixed spatial metric and energy. -/
theorem adm_scalar_constraint_time_even
    (spatialR energy cosmological : ℝ)
    (K : Fin n → Fin n → ℝ) :
    hConstraint spatialR energy cosmological
      (fun i j => -K i j) =
    hConstraint spatialR energy cosmological K := by
  simp [hConstraint, traceK_time_odd, squareK_time_even]

/-- Momentum-constraint current and extrinsic-curvature flux must both
reverse under a physical time reversal. -/
def momentumResidual (flux current : Fin n → ℝ) : Fin n → ℝ :=
  fun i => flux i - current i

theorem momentum_constraint_time_odd (flux current : Fin n → ℝ) :
    momentumResidual (fun i => -flux i) (fun i => -current i) =
       fun i => -momentumResidual flux current i := by
  funext i
  simp [momentumResidual]
  ring

end ADM

section Entanglement

variable {n : ℕ}

/-- Entanglement entropy of pure bipartite Schmidt coefficients.
The normalization ∑|a_i|²=1 is a physical state-space condition,
but the equality under conjugation does not require it. -/
noncomputable def schmidtEntropy (a : Fin n → ℂ) : ℝ :=
  -(∑ i, Complex.normSq (a i) * Real.log (Complex.normSq (a i)))

/-- A factorized spinless antiunitary conjugation preserves the Schmidt
probabilities and hence their von Neumann entropy. -/
theorem schmidt_entropy_time_even (a : Fin n → ℂ) :
    schmidtEntropy (fun i => Complex.conj (a i)) =
      schmidtEntropy a := by
  simp [schmidtEntropy, Complex.normSq_conj]

end Entanglement

section Geometry

/-- A radius and its York momentum; the two time orientations differ
by momentum sign while sharing the same radius and proper volume. -/
def reverseOrientation (s : ℝ × ℝ) : ℝ × ℝ :=
  (s.1, -s.2)

def spatialVolume (s : ℝ × ℝ) : ℝ := s.1 ^ 3

theorem reverse_twice (s : ℝ × ℝ) :
    reverseOrientation (reverseOrientation s) = s := by
  rcases s with ⟨r, p⟩
  simp [reverseOrientation]

theorem volume_time_even (s : ℝ × ℝ) :
    spatialVolume (reverseOrientation s) = spatialVolume s := by
  rfl

/-- The quotient by time reversal retains a continuum of volumes:
even perfectly paired opposite-time states at two different radii
need not have the same proper volume. -/
theorem two_sided_time_reversal_does_not_fix_volume :
    ∃ s₁ s₂ : ℝ × ℝ,
      spatialVolume (reverseOrientation s₁) = spatialVolume s₁ ∧
      spatialVolume (reverseOrientation s₂) = spatialVolume s₂ ∧
      spatialVolume s₁ ≠ spatialVolume s₂ := by
  refine ⟨(1, 1), (2, -1), rfl, rfl, ?_⟩
  norm_num [spatialVolume]

end Geometry

end GppTimeReversalVolume

#print axioms GppTimeReversalVolume.adm_scalar_constraint_time_even
#print axioms GppTimeReversalVolume.momentum_constraint_time_odd
#print axioms GppTimeReversalVolume.schmidt_entropy_time_even
#print axioms GppTimeReversalVolume.two_sided_time_reversal_does_not_fix_volume
