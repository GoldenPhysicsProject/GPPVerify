import Mathlib.NumberTheory.LSeries.Dirichlet
import GppVerify.RiemannHypothesis.CompletedLogDerivativeBridge
import Mathlib.Tactic

/-!
# Global von Mangoldt bridge

At the pinned Mathlib revision, the global prime-power logarithmic derivative is already
formalized on the half-plane of absolute convergence.  If `Λ` denotes the von Mangoldt
arithmetic function, then

  L(Λ,s) = - ζ'(s) / ζ(s),        Re s > 1.

This file records that theorem inside the GPP chain and makes explicit what has now been
closed and what remains open.

The local modules prove that each Euler factor contributes its genuine logarithmic
derivative and that, on the critical line, its real part is the Poisson/prime-power kernel
`Wp`.  The theorem below identifies the corresponding *global* arithmetic Dirichlet series
with the genuine logarithmic derivative of the analytically defined Riemann zeta function
where the Euler/Dirichlet series converges absolutely.

The remaining hard bridge is therefore analytic continuation / explicit-formula transport
from `Re s > 1` into the critical strip, together with the Archimedean completed factor.
No such continuation is smuggled into this file.
-/

namespace GppGlobalVonMangoldt

open Complex LSeries Nat
open ArithmeticFunction
open scoped LSeries.notation

/-- **Global prime-power logarithmic derivative in the absolute-convergence half-plane.**
This is Mathlib's actual von Mangoldt L-series theorem, restated in the GPP namespace. -/
theorem vonMangoldtLSeries_eq_neg_zeta_logDeriv {s : ℂ} (hs : 1 < s.re) :
    L (ArithmeticFunction.Λ : ℕ → ℂ) s =
      - deriv riemannZeta s / riemannZeta s := by
  exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- The Riemann zeta denominator occurring above is nonzero on `Re s > 1`. -/
theorem riemannZeta_ne_zero_right_half_plane {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ≠ 0 := by
  exact riemannZeta_ne_zero_of_one_lt_re hs

/-- Equivalent sign convention: the genuine global negative logarithmic derivative is
literally the von Mangoldt L-series on `Re s > 1`. -/
theorem neg_zeta_logDeriv_eq_vonMangoldtLSeries {s : ℂ} (hs : 1 < s.re) :
    -(deriv riemannZeta s / riemannZeta s) =
      L (ArithmeticFunction.Λ : ℕ → ℂ) s := by
  symm
  exact vonMangoldtLSeries_eq_neg_zeta_logDeriv hs

end GppGlobalVonMangoldt

#print axioms GppGlobalVonMangoldt.vonMangoldtLSeries_eq_neg_zeta_logDeriv
#print axioms GppGlobalVonMangoldt.riemannZeta_ne_zero_right_half_plane
#print axioms GppGlobalVonMangoldt.neg_zeta_logDeriv_eq_vonMangoldtLSeries
