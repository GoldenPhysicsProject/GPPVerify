import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# Compact mode separation and moment correction

Contributed by Daniel Toupin (Golden Physics Project), with Codex assistance.
Daniel's norm-one idele insight motivates distinguishing physical compact character
sectors from an auxiliary torus of continuously varying phases.

This file proves only the topology and algebra used in that distinction. It does not
construct the idele quotient, a Haar decomposition, an arithmetic boundary map, or RH.
The coordinate inverse estimate is uniform in the coordinate weight; identifying those
weights with an arithmetic operator is a separate analytic obligation.
-/

namespace GppCompactModeSewing

/-- A continuous phase with totally disconnected target cannot vary on a connected domain. -/
theorem phase_constant {X K : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [TopologicalSpace K] [TotallyDisconnectedSpace K]
    (phase : X → K) (hc : Continuous phase) (x y : X) : phase x = phase y :=
  TotallyDisconnectedSpace.eq_of_continuous phase hc x y

/-- A projection-commuting linear coupling has no cross block. -/
theorem cross_block_zero {A : Type*} [Ring A] (P T : A)
    (hP : P * P = P) (hc : P * T = T * P) : P * T * (1 - P) = 0 := by
  rw [hc, mul_assoc, mul_sub, mul_one, hP, sub_self, mul_zero]

/-- Successive nested projections have idempotent difference. -/
theorem difference_idempotent {A : Type*} [Ring A] (P Q : A)
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPQ : P * Q = P) (hQP : Q * P = P) :
    (Q - P) * (Q - P) = Q - P := by
  calc
    (Q - P) * (Q - P) = Q * Q - Q * P - P * Q + P * P := by noncomm_ring
    _ = Q - P := by rw [hQ, hQP, hPQ, hP]; abel

/-- An explicit right inverse removes exactly the prescribed moments. -/
theorem moment_correction {R E F : Type*} [Ring R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (M : E →ₗ[R] F) (S : F →ₗ[R] E) (hMS : ∀ y, M (S y) = y) (x : E) :
    M (x - S (M x)) = 0 := by
  rw [map_sub, hMS, sub_self]

/-- A positive spectral coordinate at least one gives a contraction on squared norm. -/
theorem inverse_coordinate_bound (a w : ℝ) (hw : 1 ≤ w) :
    a ^ 2 / w ^ 2 ≤ a ^ 2 := by
  apply div_le_self (sq_nonneg a)
  nlinarith

end GppCompactModeSewing

#print axioms GppCompactModeSewing.phase_constant
#print axioms GppCompactModeSewing.cross_block_zero
#print axioms GppCompactModeSewing.difference_idempotent
#print axioms GppCompactModeSewing.moment_correction
#print axioms GppCompactModeSewing.inverse_coordinate_bound
