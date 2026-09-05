import Mathlib.Tactic

/-!
# Principal-series light-transform density match

For the split real group `SL(2,R)`, the even and odd principal-series sectors carry the
standard hyperbolic Plancherel factors proportional respectively to

  lambda * tanh(pi*lambda/2),
  lambda * coth(pi*lambda/2).

Brown--Gowdy--Spence's normalized light-transform kernel has, on
`h = (1+i lambda)/2`, squared normalization

  rho_even(lambda) = lambda/(2*pi) * tanh(pi*lambda/2),
  rho_odd(lambda)  = lambda/(2*pi) * coth(pi*lambda/2).

The conical/principal-series block normalization used in Toupin,
`Principal-Series Kinematic Blocks for Celestial Two-Particle Cuts`, obeys

  |c(lambda)|^2 = 2*lambda/pi * coth(pi*lambda/2).

Hence its proved closed form is exactly four times the odd light-transform density.
This file formalizes only that final elementary closed-form identity.  It does not claim
that the Gamma-function evaluation of either normalization has been formalized here.
-/

namespace GppPrincipalSeriesLightPlancherelMatch

/-- Real hyperbolic cotangent, defined on the nose as reciprocal tanh. -/
def coth (x : ℝ) : ℝ := 1 / Real.tanh x

/-- Even `Z2` principal-series/light density. -/
def evenLightDensity (lambda : ℝ) : ℝ :=
  lambda / (2 * Real.pi) * Real.tanh (Real.pi * lambda / 2)

/-- Odd `Z2` principal-series/light density. -/
def oddLightDensity (lambda : ℝ) : ℝ :=
  lambda / (2 * Real.pi) * coth (Real.pi * lambda / 2)

/-- Closed form of the conical-block normalization squared. -/
def conicalBlockNormSq (lambda : ℝ) : ℝ :=
  2 * lambda / Real.pi * coth (Real.pi * lambda / 2)

/-- Exact normalization match: the conical block carries four times the odd
principal-series light-transform density. -/
theorem conicalBlockNormSq_eq_four_oddLightDensity (lambda : ℝ) :
    conicalBlockNormSq lambda = 4 * oddLightDensity lambda := by
  simp [conicalBlockNormSq, oddLightDensity]
  ring

/-- The even and odd sectors differ only by the tanh/coth replacement at the level of
the displayed closed forms. -/
theorem even_odd_closed_forms (lambda : ℝ) :
    evenLightDensity lambda =
      lambda / (2 * Real.pi) * Real.tanh (Real.pi * lambda / 2) ∧
    oddLightDensity lambda =
      lambda / (2 * Real.pi) * coth (Real.pi * lambda / 2) := by
  rfl

end GppPrincipalSeriesLightPlancherelMatch
