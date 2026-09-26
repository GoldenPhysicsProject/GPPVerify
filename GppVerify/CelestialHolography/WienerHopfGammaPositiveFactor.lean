import GppVerify.CelestialHolography.WienerHopfPositiveFactor
import GppVerify.CelestialHolography.WienerHopfGammaBridge
import Mathlib.Tactic

/-!
# Positive factorization of the base Gamma / Mehler--Fock density

The exact Wiener--Hopf/Gamma bridge gives

  Re rhoGamma(0,lambda) = (2/pi) W_ext(lambda),

while `WienerHopfPositiveFactor` gives `W_ext = a^2` with `a > 0`.
Therefore the normalized base Gamma density has the explicit positive factor

  b(lambda) = sqrt(2/pi) a(lambda),

so that `b(lambda)^2 = Re rhoGamma(0,lambda)` for every real lambda, including
the removable origin.

This is an Archimedean spectral factorization only.  It does not identify the
completed arithmetic explicit-formula kernel with a positive square and does
not prove Weil positivity or RH.
-/

namespace GppWienerHopfGammaPositiveFactor

open GppWienerHopfPositiveFactor
open GppWienerHopfGammaBridge
open GppWienerHopfWeightExtension
open GppSpectralRho

/-- Canonical positive factor of the real base Gamma spectral density. -/
noncomputable def gammaBaseFactor (lam : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) * wienerHopfFactor lam

/-- The normalization constant `2/pi` is strictly positive. -/
theorem two_div_pi_pos : 0 < (2 / Real.pi : ℝ) := by
  positivity

/-- The base Gamma factor is strictly positive for every real spectral parameter. -/
theorem gammaBaseFactor_pos (lam : ℝ) : 0 < gammaBaseFactor lam := by
  unfold gammaBaseFactor
  exact mul_pos (Real.sqrt_pos.2 two_div_pi_pos) (wienerHopfFactor_pos lam)

/-- Exact positive factorization of the real part of the base Gamma density. -/
theorem gammaBaseFactor_sq (lam : ℝ) :
    gammaBaseFactor lam ^ 2 = (rhoGamma 0 lam).re := by
  rw [rhoGamma_zero_re_eq_two_over_pi_mul_extendedWienerHopfWeight]
  unfold gammaBaseFactor
  rw [mul_pow, Real.sq_sqrt two_div_pi_pos.le, wienerHopfFactor_sq]

/-- In particular the canonical factor never vanishes. -/
theorem gammaBaseFactor_ne_zero (lam : ℝ) : gammaBaseFactor lam ≠ 0 :=
  ne_of_gt (gammaBaseFactor_pos lam)

end GppWienerHopfGammaPositiveFactor

#print axioms GppWienerHopfGammaPositiveFactor.gammaBaseFactor_pos
#print axioms GppWienerHopfGammaPositiveFactor.gammaBaseFactor_sq
