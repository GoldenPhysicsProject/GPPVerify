import Mathlib.Tactic

/-!
# Causal-diamond boundary-charge obstruction to an unconstrained York gauge quotient

The differentiable generator of geometric evolution on a bounded
spatial region is generally H = C + B, where C is a bulk gravitational
constraint and B is a boundary/corner charge. Even when variations
preserve the bulk constraint dC=0, York-volume work can be nonzero and
is then accounted for by the boundary variation dB.

This module formalizes the exact algebraic implication and its
converse. It does NOT construct the Einstein--Hilbert Iyer--Wald
surface charge or assert that it vanishes for arbitrary small diamonds.
The physical relation dH=c dV must be derived from the actual ADM/Noether
Hamiltonian with its chosen boundary data.
-/

namespace GppDiamondBoundaryCharge

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- An on-shell volume variation is carried by the boundary charge
whenever the full Hamiltonian has the York-volume differential. -/
theorem constrained_volume_work_is_boundary_charge
    (dH dC dB dV : E →ₗ[ℝ] ℝ)
    (c : ℝ)
    (hSplit : ∀ x, dH x = dC x + dB x)
    (hYork : ∀ x, dH x = c * dV x)
    (delta : E) (hConstraint : dC delta = 0) :
    dB delta = c * dV delta := by
  have h₁ := hSplit delta
  have h₂ := hYork delta
  rw [hConstraint] at h₁
  linarith

/-- Fixing the boundary charge, in addition to satisfying the
bulk constraint, fixes volume if the York work coefficient is nonzero. -/
theorem fixed_boundary_charge_forces_fixed_volume
    (dH dC dB dV : E →ₗ[ℝ] ℝ)
    (c : ℝ) (hc : c ≠ 0)
    (hSplit : ∀ x, dH x = dC x + dB x)
    (hYork : ∀ x, dH x = c * dV x)
    (delta : E) (hConstraint : dC delta = 0)
    (hBoundary : dB delta = 0) :
    dV delta = 0 := by
  have h := constrained_volume_work_is_boundary_charge
    dH dC dB dV c hSplit hYork delta hConstraint
  rw [hBoundary] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hc

/-- A nonzero admissible volume change forces a nonzero boundary
charge variation under a nondegenerate York moment-map relation. -/
theorem volume_change_requires_boundary_charge
    (dH dC dB dV : E →ₗ[ℝ] ℝ)
    (c : ℝ) (hc : c ≠ 0)
    (hSplit : ∀ x, dH x = dC x + dB x)
    (hYork : ∀ x, dH x = c * dV x)
    (delta : E) (hConstraint : dC delta = 0)
    (hVolume : dV delta ≠ 0) :
    dB delta ≠ 0 := by
  rw [constrained_volume_work_is_boundary_charge
    dH dC dB dV c hSplit hYork delta hConstraint]
  exact mul_ne_zero hc hVolume

/-- Thus nonzero constrained volume variations rule out the
identification of the full differentiable Hamiltonian with a pure
gauge constraint whose boundary charge is stationary. -/
theorem pure_gauge_interpretation_obstructed
    (dH dC dB dV : E →ₗ[ℝ] ℝ)
    (c : ℝ) (hc : c ≠ 0)
    (hSplit : ∀ x, dH x = dC x + dB x)
    (hYork : ∀ x, dH x = c * dV x)
    (delta : E) (hConstraint : dC delta = 0)
    (hVolume : dV delta ≠ 0) :
    ¬ dB delta = 0 := by
  exact volume_change_requires_boundary_charge
    dH dC dB dV c hc hSplit hYork delta hConstraint hVolume

end GppDiamondBoundaryCharge

#print axioms GppDiamondBoundaryCharge.constrained_volume_work_is_boundary_charge
#print axioms GppDiamondBoundaryCharge.fixed_boundary_charge_forces_fixed_volume
#print axioms GppDiamondBoundaryCharge.volume_change_requires_boundary_charge
