import GppVerify.CelestialHolography.ArithmeticSplitSignature
import GppVerify.RiemannHypothesis.ArithmeticSplitCoordinates

/-!
# Bridge between the two arithmetic split-coordinate conventions

`ArithmeticSplitSignature` uses `(sigma_A,tau_A)` directly as null coordinates for the
auxiliary bilinear form `2 sigma_A tau_A`.  `ArithmeticSplitCoordinates` instead uses the
canonical light-cone combinations `xi_± = sigma ± tau` for the Lorentzian form
`sigma^2 - tau^2`.

The centered coordinates themselves are identical.  The physically relevant principal-series
condition is therefore stated invariantly as `sigma = 0`, equivalently the anti-diagonal
`xi_+ = -xi_-`, and (by the existing half-density theorem) equivalently unit modulus of the
dilation character.  No claim that either auxiliary quadratic form is dynamically preferred
is made here.
-/

namespace GppArithmeticSplitConventionBridge

open GppArithmeticSplitSignature
open GppArithmeticSplitCoordinates

/-- The two files use exactly the same centered real displacement. -/
theorem sigmaA_eq_sigma (s : ℂ) : sigmaA s = sigma s := by
  rfl

/-- They also use exactly the same spectral coordinate. -/
theorem tauA_eq_tau (s : ℂ) : tauA s = tau s := by
  rfl

/-- The canonical principal-series condition is the anti-diagonal in `xi_±` coordinates. -/
theorem principal_iff_antidiagonal (s : ℂ) :
    s.re = (1 : ℝ) / 2 ↔ xiPlus s = -xiMinus s :=
  critical_line_iff_antidiagonal s

/-- Every nonreal point that is null for the auxiliary `2 sigma tau` convention lies on the
same canonical anti-diagonal principal series. -/
theorem auxiliary_splitNull_nonreal_implies_antidiagonal {s : ℂ}
    (hnull : splitFormA s = 0) (him : s.im ≠ 0) :
    xiPlus s = -xiMinus s := by
  apply (critical_line_iff_antidiagonal s).1
  rw [splitFormA_eq_zero_iff] at hnull
  exact hnull.resolve_right him

end GppArithmeticSplitConventionBridge

#print axioms GppArithmeticSplitConventionBridge.sigmaA_eq_sigma
#print axioms GppArithmeticSplitConventionBridge.principal_iff_antidiagonal
#print axioms GppArithmeticSplitConventionBridge.auxiliary_splitNull_nonreal_implies_antidiagonal
