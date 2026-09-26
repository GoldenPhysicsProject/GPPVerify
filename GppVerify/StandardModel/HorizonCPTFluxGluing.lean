import Mathlib.Tactic

/-!
# CPT horizon gluing: charge-odd, orientation-odd, energy-even

This module isolates the finite sign algebra behind a candidate two-sided horizon gluing.
Consider two CPT-related sides of a hypersurface.  Let

  q  = gauge-charge orientation,
  u  = oriented worldline / timelike-flow component,
  n  = oriented hypersurface normal.

The mirror side reverses all three:

  (q,u,n) -> (-q,-u,-n).

For a point-particle current component `j = q*u`, the two sign reversals in `q` and `u`
cancel, so the spacetime current vector itself is unchanged.  However the *oriented flux*
through the hypersurface, modeled by `j*n`, changes sign because the normal orientation is
also reversed.

By contrast a quadratic stress component `T = m*u*u` is even under `u -> -u`; its normal-
normal flux `T*n*n` is also even.  Thus a CPT-paired gluing can cancel oriented gauge
charge flux while retaining positive/even energy flux.

This is only the sign core of a possible black-hole horizon boundary condition.  It does
not prove that a physical event horizon identifies a fermion with its own CPT image, nor
does it derive annihilation or Hawking radiation.  Those require the curved spin/gauge
bundle, field equations, and quantum boundary state.
-/

namespace GppHorizonCPTFluxGluing

/-- Scalar model of one component of a gauge current. -/
def currentComponent (q u : ℝ) : ℝ := q * u

/-- Scalar model of one quadratic stress-tensor component. -/
def stressComponent (m u : ℝ) : ℝ := m * u * u

/-- Oriented current flux through a hypersurface normal. -/
def chargeFlux (q u n : ℝ) : ℝ := currentComponent q u * n

/-- Normal-normal energy flux in the same scalar sign model. -/
def energyFlux (m u n : ℝ) : ℝ := stressComponent m u * n * n

/-- Simultaneously reversing charge and worldline orientation leaves the current vector
component invariant. -/
theorem diagonal_C_T_preserves_current (q u : ℝ) :
    currentComponent (-q) (-u) = currentComponent q u := by
  simp [currentComponent]
  ring

/-- Reversing only charge flips the current. -/
theorem charge_flip_flips_current (q u : ℝ) :
    currentComponent (-q) u = - currentComponent q u := by
  simp [currentComponent]

/-- Reversing only worldline orientation also flips the current. -/
theorem orientation_flip_flips_current (q u : ℝ) :
    currentComponent q (-u) = - currentComponent q u := by
  simp [currentComponent]

/-- Under the full two-sided gluing `(q,u,n)->(-q,-u,-n)`, oriented charge flux changes
sign even though the current vector itself is unchanged. -/
theorem CPT_gluing_reverses_oriented_charge_flux (q u n : ℝ) :
    chargeFlux (-q) (-u) (-n) = - chargeFlux q u n := by
  simp [chargeFlux, currentComponent]
  ring

/-- Hence the oriented charge fluxes of the paired sides cancel exactly. -/
theorem paired_oriented_charge_flux_cancels (q u n : ℝ) :
    chargeFlux q u n + chargeFlux (-q) (-u) (-n) = 0 := by
  rw [CPT_gluing_reverses_oriented_charge_flux]
  ring

/-- Quadratic matter stress is even under worldline orientation reversal. -/
theorem orientation_flip_preserves_stress (m u : ℝ) :
    stressComponent m (-u) = stressComponent m u := by
  simp [stressComponent]
  ring

/-- The normal-normal energy flux is even under reversal of both worldline and normal
orientations. -/
theorem CPT_gluing_preserves_energy_flux (m u n : ℝ) :
    energyFlux m (-u) (-n) = energyFlux m u n := by
  simp [energyFlux, stressComponent]
  ring

/-- Thus the paired sides contribute equal, not cancelling, normal-normal energy flux. -/
theorem paired_energy_flux_adds (m u n : ℝ) :
    energyFlux m u n + energyFlux m (-u) (-n) =
      2 * energyFlux m u n := by
  rw [CPT_gluing_preserves_energy_flux]
  ring

/-- Capstone sign package for a CPT-paired hypersurface. -/
theorem horizon_CPT_sign_package (q m u n : ℝ) :
    currentComponent (-q) (-u) = currentComponent q u ∧
    chargeFlux q u n + chargeFlux (-q) (-u) (-n) = 0 ∧
    energyFlux m (-u) (-n) = energyFlux m u n := by
  exact ⟨diagonal_C_T_preserves_current q u,
    paired_oriented_charge_flux_cancels q u n,
    CPT_gluing_preserves_energy_flux m u n⟩

end GppHorizonCPTFluxGluing
