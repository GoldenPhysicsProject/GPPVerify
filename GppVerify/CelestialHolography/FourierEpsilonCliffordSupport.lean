import Mathlib.Tactic
import GppVerify.CelestialHolography.FourierSliceSupportGeometry
import GppVerify.CelestialHolography.EpsilonAnnihilatorDuality
import GppVerify.CelestialHolography.KleinSpinorIncidence

/-!
# Fourier support is the epsilon-Clifford incidence kernel

The previous finite-dimensional programme had three separately proved facts:

1. restricting the Fourier phase to a spacetime twistor line forces the dual variable
   onto the annihilator plane `W^0`;
2. epsilon middle-degree duality sends the Plucker vector of `W` to the Plucker vector
   of `W^0` without a metric;
3. the same Klein bivector acts by Clifford multiplication between the two chiral
   twistor modules, with kernel `W^0` on the dual side.

This file identifies them exactly.  On the graph chart, the two scalar Fourier support
constraints are equivalent to the single epsilon-Clifford equation

  cMinus(chartPlucker(A)) xi = 0.

Thus the strongest canonical finite-dimensional chain is

  Fourier support = annihilator incidence = epsilon duality = chiral Clifford kernel.

No `V* -> V` polarity, Hodge star, orientation reversal, or nonlinear Einstein claim is
used in this theorem.
-/

namespace GppFourierEpsilonCliffordSupport

open GppGrassmannianGooglyDecomposition
open GppTwistorAnnihilatorIncidence
open GppIncidenceKernelGoogly
open GppFourierSliceSupportGeometry
open GppEpsilonAnnihilatorDuality
open GppKleinSpinorIncidence

/-- The two notations used for a general annihilator-plane vector agree exactly. -/
theorem dualLineVector_eq_annihilatorVector
    (a b c d t u : ℝ) :
    dualLineVector a b c d t u = annihilatorVector a b c d t u := by
  apply Prod.ext
  · simp [dualLineVector, annihilatorVector]
    ring
  · apply Prod.ext
    · simp [dualLineVector, annihilatorVector]
      ring
    · apply Prod.ext <;> simp [dualLineVector, annihilatorVector]

/-- Main canonical support theorem: the two restricted Fourier phase constraints vanish
iff the Fourier-dual variable lies in the epsilon-Clifford kernel of the same Klein point. -/
theorem fourier_constraints_iff_clifford_kernel
    (a b c d : ℝ) (ξ : V4) :
    (phaseConstraint1 a b ξ = 0 ∧ phaseConstraint2 c d ξ = 0) ↔
      cMinus (chartPlucker (a,b,c,d)) ξ = (0,0,0,0) := by
  constructor
  · intro h
    have hline := (constraints_iff_on_annihilator a b c d ξ).mp h
    apply (cMinus_kernel_is_annihilator_line a b c d ξ).2
    rw [← dualLineVector_eq_annihilatorVector]
    exact hline
  · intro h
    have hline := (cMinus_kernel_is_annihilator_line a b c d ξ).1 h
    apply (constraints_iff_on_annihilator a b c d ξ).2
    rw [dualLineVector_eq_annihilatorVector]
    exact hline

/-- Equivalent intrinsic statement: a dual variable pairs to zero with every twistor on
the spacetime line iff it lies in the epsilon-Clifford kernel. -/
theorem phase_zero_on_plane_iff_clifford_kernel
    (a b c d : ℝ) (ξ : V4) :
    (∀ r s : ℝ, pair4 (lineVector a b c d r s) ξ = 0) ↔
      cMinus (chartPlucker (a,b,c,d)) ξ = (0,0,0,0) := by
  rw [← constraints_iff_phase_zero_on_plane]
  exact fourier_constraints_iff_clifford_kernel a b c d ξ

/-- Plane-level coordinate companion: epsilon dual of the source Plucker vector is the
Plucker vector of the Fourier-support/annihilator plane. -/
theorem epsilon_dual_is_fourier_support_plane
    (a b c d : ℝ) :
    epsilonDualPlucker (chartPlucker (a,b,c,d)) = annihilatorPlucker a b c d := by
  exact epsilonDual_chart_eq_annihilatorPlucker a b c d

/-- The Fourier-support plane is Klein-null, confirming that it is itself a decomposable
2-plane in the dual twistor space. -/
theorem fourier_support_plane_is_klein_null
    (a b c d : ℝ) :
    kleinQ (epsilonDualPlucker (chartPlucker (a,b,c,d))) = 0 := by
  rw [epsilon_dual_is_fourier_support_plane]
  exact annihilatorPlucker_klein_null a b c d

/-- Canonical finite-dimensional capstone, free of any chosen metric polarity. -/
theorem canonical_fourier_epsilon_incidence_capstone
    (a b c d : ℝ) (ξ : V4) :
    ((phaseConstraint1 a b ξ = 0 ∧ phaseConstraint2 c d ξ = 0) ↔
       cMinus (chartPlucker (a,b,c,d)) ξ = (0,0,0,0)) ∧
    epsilonDualPlucker (chartPlucker (a,b,c,d)) = annihilatorPlucker a b c d ∧
    kleinQ (epsilonDualPlucker (chartPlucker (a,b,c,d))) = 0 := by
  exact ⟨fourier_constraints_iff_clifford_kernel a b c d ξ,
    epsilon_dual_is_fourier_support_plane a b c d,
    fourier_support_plane_is_klein_null a b c d⟩

end GppFourierEpsilonCliffordSupport
