import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
# Abstract Gibbs cumulant differential algebra

For an exponential-family moment hierarchy with

  Z'  = -M1,
  M1' = -M2,
  M2' = -M3,
  M3' = -M4,

the normalized third cumulant differentiates to minus the normalized fourth
cumulant.  This file isolates the quotient-rule algebra independently of zeta,
so the arithmetic Gibbs specialization only has to prove the raw-moment derivative
hierarchy and nonvanishing of the partition function.

The same cumulant algebra also gives an exact translation-invariant formula for
the covariance determinant of the two observables `X` and `X^2`.  If `mu` is the
mean and `kappa2`, `kappa3`, `kappa4` are the second through fourth cumulants, then

  Var(X) = kappa2,
  Cov(X,X^2) = kappa3 + 2 mu kappa2,
  Var(X^2) = kappa4 + 4 mu kappa3 + 4 mu^2 kappa2 + 2 kappa2^2.

The mean cancels from the determinant:

  det Cov(X,X^2) = kappa2*kappa4 + 2*kappa2^3 - kappa3^2.

This identity is purely algebraic and applies equally to any probability-normalized
exponential family once its cumulants are identified.
-/

namespace GppGibbsCumulantDifferentialAlgebra

/-- Third cumulant written in terms of unnormalized moments. -/
noncomputable def kappa3Expr
    (Z M1 M2 M3 : ℝ → ℝ) (β : ℝ) : ℝ :=
  M3 β / Z β -
    3 * (M2 β / Z β) * (M1 β / Z β) +
    2 * (M1 β / Z β) ^ 3

/-- Fourth cumulant written in terms of unnormalized moments. -/
noncomputable def kappa4Expr
    (Z M1 M2 M3 M4 : ℝ → ℝ) (β : ℝ) : ℝ :=
  M4 β / Z β -
    4 * (M3 β / Z β) * (M1 β / Z β) -
    3 * (M2 β / Z β) ^ 2 +
    12 * (M2 β / Z β) * (M1 β / Z β) ^ 2 -
    6 * (M1 β / Z β) ^ 4

/-- The covariance entry `Cov(X,X^2)` expressed through the mean and the second
and third cumulants. -/
def covXXSqFromCumulants (mu kappa2 kappa3 : ℝ) : ℝ :=
  kappa3 + 2 * mu * kappa2

/-- The variance of `X^2` expressed through the mean and cumulants through order four. -/
def varXSqFromCumulants (mu kappa2 kappa3 kappa4 : ℝ) : ℝ :=
  kappa4 + 4 * mu * kappa3 + 4 * mu ^ 2 * kappa2 + 2 * kappa2 ^ 2

/-- Covariance determinant of the observables `X` and `X^2`, written in cumulant
coordinates before cancellation of the mean. -/
def covarianceDetFromCumulants (mu kappa2 kappa3 kappa4 : ℝ) : ℝ :=
  kappa2 * varXSqFromCumulants mu kappa2 kappa3 kappa4 -
    (covXXSqFromCumulants mu kappa2 kappa3) ^ 2

/-- **Translation-invariant cumulant determinant identity.**  The covariance
determinant of `X` and `X^2` is independent of the mean and equals
`kappa2*kappa4 + 2*kappa2^3 - kappa3^2`. -/
theorem covarianceDetFromCumulants_eq
    (mu kappa2 kappa3 kappa4 : ℝ) :
    covarianceDetFromCumulants mu kappa2 kappa3 kappa4 =
      kappa2 * kappa4 + 2 * kappa2 ^ 3 - kappa3 ^ 2 := by
  unfold covarianceDetFromCumulants covXXSqFromCumulants varXSqFromCumulants
  ring

/-- **Universal exponential-family cumulant law**:
if the unnormalized moments satisfy the canonical derivative ladder, then
`kappa3' = -kappa4`. -/
theorem hasDerivAt_kappa3Expr
    {Z M1 M2 M3 M4 : ℝ → ℝ} {β : ℝ}
    (hZ : HasDerivAt Z (-M1 β) β)
    (h1 : HasDerivAt M1 (-M2 β) β)
    (h2 : HasDerivAt M2 (-M3 β) β)
    (h3 : HasDerivAt M3 (-M4 β) β)
    (hZne : Z β ≠ 0) :
    HasDerivAt (kappa3Expr Z M1 M2 M3)
      (-(kappa4Expr Z M1 M2 M3 M4 β)) β := by
  have hM3Z := HasDerivAt.div h3 hZ hZne
  have hM2Z := HasDerivAt.div h2 hZ hZne
  have hM1Z := HasDerivAt.div h1 hZ hZne
  have hprod := HasDerivAt.mul hM2Z hM1Z
  have hcubic := HasDerivAt.pow hM1Z 3
  have hsum := HasDerivAt.add (HasDerivAt.sub hM3Z (HasDerivAt.const_mul 3 hprod))
    (HasDerivAt.const_mul 2 hcubic)
  refine (hsum.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · simp only [kappa4Expr, Pi.div_apply, show (3 : ℕ) - 1 = 2 from rfl]
    field_simp
    ring
  · simp only [kappa3Expr, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    ring

end GppGibbsCumulantDifferentialAlgebra

#print axioms GppGibbsCumulantDifferentialAlgebra.covarianceDetFromCumulants_eq
#print axioms GppGibbsCumulantDifferentialAlgebra.hasDerivAt_kappa3Expr
