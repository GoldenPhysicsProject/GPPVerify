import GppVerify.RiemannHypothesis.VonMangoldtCubicPositivity
import GppVerify.RiemannHypothesis.ZetaGibbsMoments
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Von Mangoldt cumulant derivatives of `-ζ'/ζ`

On the open half-plane `Re s > 1`, the genuine negative logarithmic derivative
of zeta agrees pointwise with the von Mangoldt L-series. Equality on an open set
therefore transports to all iterated derivatives. Combining this with Mathlib's
L-series derivative theorem gives the full alternating logarithmic-insertion hierarchy.
-/

namespace GppVonMangoldtCumulantDerivativeBridge

open Complex LSeries
open GppGlobalVonMangoldt
open GppVonMangoldtCumulantSummability
open GppVonMangoldtCubicPositivity
open GppZetaGibbsMoments
open scoped LSeries.notation ArithmeticFunction Topology

/-- Genuine negative zeta logarithmic derivative. -/
noncomputable def negZetaLogDeriv (s : ℂ) : ℂ :=
  -(deriv riemannZeta s / riemannZeta s)

/-- Pointwise von Mangoldt identity on the honest half-plane. -/
theorem negZetaLogDeriv_eqOn_vonMangoldtLSeries :
    zetaHalfPlane.EqOn negZetaLogDeriv (LSeries vonMangoldtComplex) := by
  intro s hs
  unfold negZetaLogDeriv
  exact neg_zeta_logDeriv_eq_vonMangoldtLSeries hs

/-- Full derivative hierarchy: the `m`th derivative of `-ζ'/ζ` inserts `m`
logarithms into the von Mangoldt coefficients and contributes the sign `(-1)^m`. -/
theorem iteratedDeriv_negZetaLogDeriv_eq_logMomentLSeries
    (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv m negZetaLogDeriv s =
      (-1 : ℂ) ^ m * LSeries ((LSeries.logMul^[m]) vonMangoldtComplex) s := by
  have heq :
      iteratedDeriv m negZetaLogDeriv s =
        iteratedDeriv m (LSeries vonMangoldtComplex) s := by
    exact
      (negZetaLogDeriv_eqOn_vonMangoldtLSeries.iteratedDeriv_of_isOpen
        isOpen_zetaHalfPlane m) hs
  rw [heq]
  have hsE : (1 : EReal) < (s.re : EReal) := by
    exact_mod_cast hs
  have habs : LSeries.abscissaOfAbsConv vonMangoldtComplex < (s.re : EReal) :=
    lt_of_le_of_lt abscissa_vonMangoldtComplex_le_one hsE
  exact LSeries_iteratedDeriv m habs

/-- **Exact cubic derivative bridge**:
`(-ζ'/ζ)''` equals the twice-logarithm-weighted von Mangoldt L-series on `Re s>1`. -/
theorem iteratedDeriv_two_negZetaLogDeriv_eq_logMul_logMul
    {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv 2 negZetaLogDeriv s =
      LSeries (LSeries.logMul (LSeries.logMul vonMangoldtComplex)) s := by
  simpa [Function.iterate_succ_apply] using
    (iteratedDeriv_negZetaLogDeriv_eq_logMomentLSeries 2 hs)

/-- Fourth-cumulant raw response: the third derivative of `-ζ'/ζ` is minus the
three-logarithm-weighted von Mangoldt series. -/
theorem iteratedDeriv_three_negZetaLogDeriv_eq_neg_logMul_three
    {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv 3 negZetaLogDeriv s =
      -LSeries
        (LSeries.logMul
          (LSeries.logMul
            (LSeries.logMul vonMangoldtComplex))) s := by
  rw [iteratedDeriv_negZetaLogDeriv_eq_logMomentLSeries 3 hs]
  norm_num [Function.iterate_succ_apply]

/-- On the real Gibbs axis, the second derivative of `-ζ'/ζ` has strictly positive
real part. -/
theorem iteratedDeriv_two_negZetaLogDeriv_re_pos
    {β : ℝ} (hβ : 1 < β) :
    0 < (iteratedDeriv 2 negZetaLogDeriv (β : ℂ)).re := by
  rw [iteratedDeriv_two_negZetaLogDeriv_eq_logMul_logMul
    (show 1 < ((β : ℂ).re) by simpa using hβ)]
  exact logMul_logMul_vonMangoldt_re_pos hβ

end GppVonMangoldtCumulantDerivativeBridge

#print axioms GppVonMangoldtCumulantDerivativeBridge.iteratedDeriv_negZetaLogDeriv_eq_logMomentLSeries
#print axioms GppVonMangoldtCumulantDerivativeBridge.iteratedDeriv_two_negZetaLogDeriv_eq_logMul_logMul
#print axioms GppVonMangoldtCumulantDerivativeBridge.iteratedDeriv_three_negZetaLogDeriv_eq_neg_logMul_three
#print axioms GppVonMangoldtCumulantDerivativeBridge.iteratedDeriv_two_negZetaLogDeriv_re_pos
