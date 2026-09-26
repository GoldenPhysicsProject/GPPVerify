import GppVerify.RiemannHypothesis.ArithmeticConformalKinematics
import GppVerify.RiemannHypothesis.CasimirIdentity
import Mathlib.Tactic

/-!
# Arithmetic conformal Casimir on the one-dimensional scale sector

The logarithmic-scale character

  psi_tau(x) = exp(i tau x)

carries the principal-series parameter `s = 1/2 + i tau`.  The quadratic
Weyl-invariant combination

  C(s) = s(1-s)

is fixed by arithmetic shadow and becomes exactly

  C(1/2+i tau) = 1/4 + tau^2.

Equivalently the standard `sl(2)` primary Casimir `s(s-1)` is
`-(1/4+tau^2)`.  Thus the same real parameter `tau` that is Fourier momentum
for logarithmic scale is also the principal-series Casimir momentum.

This is an exact global-conformal/representation-theoretic statement.  It does
not yet construct the operator algebra or OPE data of a full one-dimensional
CFT, and it makes no statement about zeta-zero occupancy.
-/

namespace GppArithmeticConformalCasimir

open Complex
open GppArithmeticConformalKinematics

/-- The shadow-invariant quadratic principal-series parameter. -/
def arithmeticCasimir (s : ℂ) : ℂ := s * (1 - s)

/-- Arithmetic Weyl/shadow reflection preserves the quadratic Casimir. -/
theorem arithmeticCasimir_shadow (s : ℂ) :
    arithmeticCasimir (1 - s) = arithmeticCasimir s := by
  unfold arithmeticCasimir
  ring

/-- On the half-density principal line the positive-sign arithmetic Casimir is
exactly `1/4 + tau^2`. -/
theorem arithmeticCasimir_principal (tau : ℝ) :
    arithmeticCasimir (principalParameter tau) =
      (1 / 4 : ℂ) + (tau : ℂ) ^ 2 := by
  unfold arithmeticCasimir principalParameter
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination -((tau : ℂ) ^ 2) * hI

/-- The conventional `sl(2)` primary Casimir `s(s-1)` has the opposite sign. -/
theorem sl2Casimir_principal (tau : ℝ) :
    principalParameter tau * (principalParameter tau - 1) =
      -((1 / 4 : ℂ) + (tau : ℂ) ^ 2) := by
  rw [← arithmeticCasimir_principal tau]
  unfold arithmeticCasimir
  ring

/-- The parameter convention in the earlier Casimir module agrees exactly after
`lambda = 2 tau`. -/
theorem hWeight_two_mul_eq_principalParameter (tau : ℝ) :
    GppCasimirIdentity.hWeight (2 * tau) = principalParameter tau := by
  unfold GppCasimirIdentity.hWeight principalParameter
  push_cast
  ring

/-- Likewise its Riemann variable is the same half-density parameter. -/
theorem sCritical_two_mul_eq_principalParameter (tau : ℝ) :
    GppCasimirIdentity.sCritical (2 * tau) = principalParameter tau := by
  unfold GppCasimirIdentity.sCritical principalParameter
  push_cast
  ring

/-- The previously formalized `sl(2)`/Riemann Casimir identity is therefore
literally the same dispersion law as the logarithmic-scale principal character. -/
theorem inherited_casimir_identity (tau : ℝ) :
    principalParameter tau * (principalParameter tau - 1) =
      -(principalParameter tau * (1 - principalParameter tau)) := by
  have h := GppCasimirIdentity.casimir_eq_neg_riemann_form (2 * tau)
  simpa [hWeight_two_mul_eq_principalParameter,
    sCritical_two_mul_eq_principalParameter] using h

/-- Shadow reverses scale momentum but leaves its Casimir energy unchanged. -/
theorem principal_shadow_preserves_casimir (tau : ℝ) :
    arithmeticCasimir (principalParameter (-tau)) =
      arithmeticCasimir (principalParameter tau) := by
  rw [← shadow_principalParameter tau]
  exact arithmeticCasimir_shadow (principalParameter tau)

end GppArithmeticConformalCasimir

#print axioms GppArithmeticConformalCasimir.arithmeticCasimir_shadow
#print axioms GppArithmeticConformalCasimir.arithmeticCasimir_principal
#print axioms GppArithmeticConformalCasimir.sl2Casimir_principal
#print axioms GppArithmeticConformalCasimir.inherited_casimir_identity
#print axioms GppArithmeticConformalCasimir.principal_shadow_preserves_casimir
