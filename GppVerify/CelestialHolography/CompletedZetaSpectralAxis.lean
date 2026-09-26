import GppVerify.CelestialHolography.CompletedZetaPrincipalSeriesResponse
import Mathlib.Tactic

/-!
# Completed-zeta response on the parameterized celestial principal axis

Under the exact positive-real dictionary `Delta = 2s`, write

  s = 1/2 + i tau,
  Delta(tau) = 1 + 2 i tau.

This file packages the already-proved principal-series statements directly in the
real spectral parameter `tau`.  Celestial shadow acts by `tau -> -tau`, and the
`-i` normalized completed-zeta logarithmic response is real and odd in `tau`, away
from zeros where the logarithmic derivative is undefined.  No assertion is made
that any zero lies on this axis.
-/

namespace GppCompletedZetaSpectralAxis

open Complex
open GppPositiveReal
open GppCompletedZetaPrincipalSeriesResponse

/-- Parameterization of the scalar celestial principal series induced by
`s = 1/2 + i tau` and `Delta = 2s`. -/
def principalDelta (tau : ℝ) : ℂ :=
  1 + (2 * tau : ℂ) * Complex.I

/-- The parameterized spectral line is exactly the celestial unitary axis. -/
@[simp] theorem principalDelta_re (tau : ℝ) :
    (principalDelta tau).re = 1 := by
  simp [principalDelta]

/-- Celestial shadow reverses the real principal-series spectral parameter. -/
theorem celestialShadow_principalDelta (tau : ℝ) :
    celestialShadow (principalDelta tau) = principalDelta (-tau) := by
  apply Complex.ext <;> simp [celestialShadow, principalDelta] <;> ring

/-- Complex conjugation has the same action `tau -> -tau` on the principal axis. -/
theorem complexConj_principalDelta (tau : ℝ) :
    complexConj (principalDelta tau) = principalDelta (-tau) := by
  apply Complex.ext <;> simp [complexConj, principalDelta] <;> ring

/-- The completed-zeta logarithmic response is purely imaginary on the explicit
principal-series parameterization, away from zeros. -/
theorem celestialCompletedResponse_re_eq_zero_at_tau
    (tau : ℝ)
    (hLambda : GppCompletedZetaDerivative.completedRiemannZeta
      (principalDelta tau / 2) ≠ 0) :
    (celestialCompletedResponse (principalDelta tau)).re = 0 := by
  exact celestialCompletedResponse_re_eq_zero (principalDelta_re tau) hLambda

/-- The `-i` normalized completed-zeta response is real on the explicit spectral
axis, away from zeros. -/
theorem celestialCompletedPhaseResponse_im_eq_zero_at_tau
    (tau : ℝ)
    (hLambda : GppCompletedZetaDerivative.completedRiemannZeta
      (principalDelta tau / 2) ≠ 0) :
    (celestialCompletedPhaseResponse (principalDelta tau)).im = 0 := by
  exact celestialCompletedPhaseResponse_im_eq_zero (principalDelta_re tau) hLambda

/-- The parameterized principal-axis points never hit the completed-zeta poles
`Delta = 0` or `Delta = 2`. -/
theorem principalDelta_ne_zero (tau : ℝ) : principalDelta tau ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simpa using hre

 theorem principalDelta_ne_two (tau : ℝ) : principalDelta tau ≠ 2 := by
  intro h
  have hre := congrArg Complex.re h
  simp [principalDelta] at hre

/-- **Spectral oddness.**  The real phase-generator response changes sign under
`tau -> -tau`.  The single nonvanishing hypothesis at `tau` is enough because the
functional equation used by the inherited shadow theorem transports it to the
reflected point. -/
theorem celestialCompletedPhaseResponse_odd_tau
    (tau : ℝ)
    (hLambda : GppCompletedZetaDerivative.completedRiemannZeta
      (principalDelta tau / 2) ≠ 0) :
    celestialCompletedPhaseResponse (principalDelta tau) =
      -celestialCompletedPhaseResponse (principalDelta (-tau)) := by
  rw [← celestialShadow_principalDelta tau]
  exact celestialCompletedPhaseResponse_shadow_odd
    (principalDelta_ne_zero tau) (principalDelta_ne_two tau) hLambda

end GppCompletedZetaSpectralAxis

#print axioms GppCompletedZetaSpectralAxis.principalDelta_re
#print axioms GppCompletedZetaSpectralAxis.celestialShadow_principalDelta
#print axioms GppCompletedZetaSpectralAxis.complexConj_principalDelta
#print axioms GppCompletedZetaSpectralAxis.celestialCompletedResponse_re_eq_zero_at_tau
#print axioms GppCompletedZetaSpectralAxis.celestialCompletedPhaseResponse_im_eq_zero_at_tau
#print axioms GppCompletedZetaSpectralAxis.principalDelta_ne_zero
#print axioms GppCompletedZetaSpectralAxis.principalDelta_ne_two
#print axioms GppCompletedZetaSpectralAxis.celestialCompletedPhaseResponse_odd_tau
