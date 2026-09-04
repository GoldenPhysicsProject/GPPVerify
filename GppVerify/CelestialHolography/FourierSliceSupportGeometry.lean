import Mathlib.Tactic
import GppVerify.CelestialHolography.IncidenceKernelGoogly

/-!
# Fourier-slice support geometry on the twistor big cell

For a graph 2-plane `W_A`, restricting the four-dimensional Fourier phase to the
plane leaves a two-dimensional phase.  Integration over the plane therefore imposes
two linear constraints on the Fourier variable.  This module proves that the common
zero locus of those constraints is exactly the annihilator 2-plane already used in the
incidence-kernel construction.

This is the finite-dimensional algebraic core of the Fourier-slice theorem.  No delta
distributions or integrals are asserted here.
-/

namespace GppFourierSliceSupportGeometry

open GppTwistorAnnihilatorIncidence
open GppIncidenceKernelGoogly

/-- First Fourier constraint after restricting the phase to the graph plane. -/
def phaseConstraint1 (a b : ℝ) (ξ : V4) : ℝ :=
  ξ.1 + a*ξ.2.2.1 + b*ξ.2.2.2

/-- Second Fourier constraint after restricting the phase to the graph plane. -/
def phaseConstraint2 (c d : ℝ) (ξ : V4) : ℝ :=
  ξ.2.1 + c*ξ.2.2.1 + d*ξ.2.2.2

/-- The ambient pairing with a graph-line point factors through the two plane
constraints. -/
theorem restricted_phase_factorization
    (a b c d r s : ℝ) (ξ : V4) :
    pair4 (lineVector a b c d r s) ξ =
      r * phaseConstraint1 a b ξ + s * phaseConstraint2 c d ξ := by
  simp [pair4, lineVector, phaseConstraint1, phaseConstraint2]
  ring

/-- Every point of the canonical annihilator plane solves both Fourier support
constraints. -/
theorem dualLineVector_solves_constraints
    (a b c d t u : ℝ) :
    phaseConstraint1 a b (dualLineVector a b c d t u) = 0 ∧
    phaseConstraint2 c d (dualLineVector a b c d t u) = 0 := by
  constructor <;> simp [phaseConstraint1, phaseConstraint2, dualLineVector] <;> ring

/-- Conversely, every Fourier variable satisfying the two support constraints is
exactly the annihilator-plane vector obtained by taking its last two coordinates as
parameters. -/
theorem constraints_parameterize_annihilator
    (a b c d : ℝ) (ξ : V4)
    (h1 : phaseConstraint1 a b ξ = 0)
    (h2 : phaseConstraint2 c d ξ = 0) :
    ξ = dualLineVector a b c d ξ.2.2.1 ξ.2.2.2 := by
  rcases ξ with ⟨x0,x1,x2,x3⟩
  simp only [phaseConstraint1, phaseConstraint2] at h1 h2
  simp only [dualLineVector]
  apply Prod.ext
  · dsimp at h1 ⊢
    linarith
  · apply Prod.ext
    · dsimp at h2 ⊢
      linarith
    · apply Prod.ext
      · rfl
      · rfl

/-- Exact support equivalence: the restricted Fourier phase is stationary in both
plane parameters iff the Fourier variable lies on the annihilator dual plane. -/
theorem constraints_iff_on_annihilator
    (a b c d : ℝ) (ξ : V4) :
    (phaseConstraint1 a b ξ = 0 ∧ phaseConstraint2 c d ξ = 0) ↔
      ξ = dualLineVector a b c d ξ.2.2.1 ξ.2.2.2 := by
  constructor
  · rintro ⟨h1,h2⟩
    exact constraints_parameterize_annihilator a b c d ξ h1 h2
  · intro h
    rw [h]
    exact dualLineVector_solves_constraints a b c d ξ.2.2.1 ξ.2.2.2

/-- If the Fourier support constraints vanish, the ambient phase vanishes on every
point of the original graph plane. -/
theorem support_constraints_force_incidence
    (a b c d : ℝ) (ξ : V4)
    (h1 : phaseConstraint1 a b ξ = 0)
    (h2 : phaseConstraint2 c d ξ = 0)
    (r s : ℝ) :
    pair4 (lineVector a b c d r s) ξ = 0 := by
  rw [restricted_phase_factorization, h1, h2]
  ring

end GppFourierSliceSupportGeometry
