import Mathlib.Analysis.Calculus.Deriv.Basic
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
  have hM3Z := h3.div hZ hZne
  have hM2Z := h2.div hZ hZne
  have hM1Z := h1.div hZ hZne
  have hprod := hM2Z.mul hM1Z
  have hcubic := hM1Z.pow 3
  have hsum := hM3Z.sub (hprod.const_mul 3) |>.add (hcubic.const_mul 2)
  convert hsum using 1
  · funext x
    simp [kappa3Expr]
    ring
  · simp [kappa4Expr]
    field_simp [hZne]
    ring

end GppGibbsCumulantDifferentialAlgebra

#print axioms GppGibbsCumulantDifferentialAlgebra.covarianceDetFromCumulants_eq
#print axioms GppGibbsCumulantDifferentialAlgebra.hasDerivAt_kappa3Expr
