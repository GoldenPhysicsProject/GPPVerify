import GppVerify.CelestialHolography.WienerHopfWeightExtension
import Mathlib.Tactic

/-!
# Positive square-root factor of the Wiener--Hopf spectral weight

The continuously extended weight

  W(lambda) = pi lambda / sinh(pi lambda),   W(0)=1,

is strictly positive.  Hence it has the canonical real factor

  a(lambda)=sqrt(W(lambda))

with `a(lambda)^2=W(lambda)`.  This is the pointwise positive-factor ingredient
needed when comparing the Archimedean spectral channel with the arithmetic
`A^*A` architecture.  It does not identify this weight with the full completed
arithmetic kernel or prove RH.
-/

namespace GppWienerHopfPositiveFactor

open GppWienerHopfWeightExtension

/-- Canonical positive square-root factor of the extended Wiener--Hopf weight. -/
noncomputable def wienerHopfFactor (lam : ℝ) : ℝ :=
  Real.sqrt (extendedWienerHopfWeight lam)

/-- The factor is strictly positive everywhere. -/
theorem wienerHopfFactor_pos (lam : ℝ) :
    0 < wienerHopfFactor lam := by
  unfold wienerHopfFactor
  exact Real.sqrt_pos.2 (extendedWienerHopfWeight_pos lam)

/-- Exact positive factorization of the spectral weight. -/
theorem wienerHopfFactor_sq (lam : ℝ) :
    wienerHopfFactor lam ^ 2 = extendedWienerHopfWeight lam := by
  unfold wienerHopfFactor
  exact Real.sq_sqrt (extendedWienerHopfWeight_pos lam).le

/-- The factor never vanishes. -/
theorem wienerHopfFactor_ne_zero (lam : ℝ) :
    wienerHopfFactor lam ≠ 0 :=
  ne_of_gt (wienerHopfFactor_pos lam)

end GppWienerHopfPositiveFactor

#print axioms GppWienerHopfPositiveFactor.wienerHopfFactor_pos
#print axioms GppWienerHopfPositiveFactor.wienerHopfFactor_sq
