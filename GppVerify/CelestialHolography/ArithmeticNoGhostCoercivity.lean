import Mathlib

/-!
# Arithmetic no-ghost coercivity skeleton

The global AFT target is a coercive estimate for the odd Laplacian on the
completed Tate boundary complex.  Abstractly, if an odd-sector energy satisfies

  c * ‖x‖² ≤ E(x),    c > 0,

then every harmonic vector `E(x)=0` must vanish.  This is the exact elementary
implication needed after the arithmetic construction supplies the correct
closed differential, graph topology, and odd energy.

This file deliberately does not construct that arithmetic differential or
prove the coercive estimate itself, and therefore makes no claim of RH.
-/

namespace GppArithmeticNoGhost

/-- Positive coercivity excludes nonzero zero-energy vectors. -/
theorem coercive_zero_energy_vanish
    {E : Type*} [NormedAddCommGroup E]
    (energy : E → ℝ) (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ x, c * ‖x‖ ^ 2 ≤ energy x)
    {x : E} (hx : energy x = 0) :
    x = 0 := by
  by_contra hne
  have hnorm : 0 < ‖x‖ := (norm_pos_iff.mpr hne)
  have hsquare : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hnorm
  have hpositive : 0 < c * ‖x‖ ^ 2 := mul_pos hc hsquare
  have hbound := hcoercive x
  rw [hx] at hbound
  linarith

/-- The same no-ghost implication when harmonicity is expressed by a vanishing
odd Laplacian quadratic form. -/
theorem coercive_odd_harmonic_vanish
    {E : Type*} [NormedAddCommGroup E]
    (oddEnergy : E → ℝ) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ x, c * ‖x‖ ^ 2 ≤ oddEnergy x)
    {x : E} (hharmonic : oddEnergy x = 0) :
    x = 0 :=
  coercive_zero_energy_vanish oddEnergy c hc hgap hharmonic

/-- A uniform positive lower spectral bound immediately rules out a ghost
sequence of unit vectors with energy tending to zero.  This finite inequality
is the algebraic form of the "no escaped odd zero mode" requirement. -/
theorem unit_vector_energy_lower_bound
    {E : Type*} [NormedAddCommGroup E]
    (energy : E → ℝ) (c : ℝ)
    (hcoercive : ∀ x, c * ‖x‖ ^ 2 ≤ energy x)
    {x : E} (hx : ‖x‖ = 1) :
    c ≤ energy x := by
  simpa [hx] using hcoercive x

end GppArithmeticNoGhost

#print axioms GppArithmeticNoGhost.coercive_zero_energy_vanish
#print axioms GppArithmeticNoGhost.coercive_odd_harmonic_vanish
#print axioms GppArithmeticNoGhost.unit_vector_energy_lower_bound
