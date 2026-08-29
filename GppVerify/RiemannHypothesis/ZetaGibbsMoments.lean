import GppVerify.RiemannHypothesis.ZetaGibbsSummability
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Zeta derivatives as logarithmic Gibbs moments

On the half-plane `Re s > 1`, the Riemann zeta function is exactly the L-series
with constant coefficient one.  Equality on this open half-plane transports to all
iterated derivatives.  Mathlib's `LSeries_iteratedDeriv` then identifies the `m`th
zeta derivative with `(-1)^m` times the L-series whose coefficients carry `m`
logarithmic factors.

This is an absolute-convergence statement only; no positivity is analytically
continued into the critical strip.
-/

namespace GppZetaGibbsMoments

open Complex LSeries

open scoped LSeries.notation Topology

/-- The honest Dirichlet-series half-plane. -/
def zetaHalfPlane : Set ℂ := {s | 1 < s.re}

lemma isOpen_zetaHalfPlane : IsOpen zetaHalfPlane := by
  exact isOpen_lt continuous_const continuous_re

/-- On `Re s > 1`, zeta is exactly the L-series with constant coefficient `1`. -/
theorem riemannZeta_eq_LSeries_one {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = LSeries (fun _ : ℕ => (1 : ℂ)) s := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term, Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
  · simp [LSeries.term_of_ne_zero hn]

/-- Pointwise equality of zeta and the constant-one L-series on the honest half-plane. -/
theorem riemannZeta_eqOn_LSeries_one :
    zetaHalfPlane.EqOn riemannZeta (LSeries (fun _ : ℕ => (1 : ℂ))) := by
  intro s hs
  exact riemannZeta_eq_LSeries_one hs

/-- All iterated derivatives agree on the Dirichlet-series half-plane. -/
theorem iteratedDeriv_riemannZeta_eq_iteratedDeriv_LSeries_one
    (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv m riemannZeta s =
      iteratedDeriv m (LSeries (fun _ : ℕ => (1 : ℂ))) s := by
  exact (riemannZeta_eqOn_LSeries_one.iteratedDeriv_of_isOpen
    isOpen_zetaHalfPlane m) hs

/-- The full logarithmic-moment hierarchy for zeta in `Re s > 1`. -/
theorem iteratedDeriv_riemannZeta_eq_logMomentLSeries
    (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv m riemannZeta s =
      (-1 : ℂ) ^ m * LSeries (LSeries.logMul^[m] (fun _ : ℕ => (1 : ℂ))) s := by
  rw [iteratedDeriv_riemannZeta_eq_iteratedDeriv_LSeries_one m hs]
  apply LSeries_iteratedDeriv
  exact GppZetaGibbsSummability.constant_abscissa_le_one.trans_lt
    (by exact_mod_cast hs)

/-- First derivative: one logarithmic insertion. -/
theorem deriv_riemannZeta_eq_neg_logMomentLSeries {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta s = -LSeries (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) s := by
  simpa [iteratedDeriv_one] using
    (iteratedDeriv_riemannZeta_eq_logMomentLSeries 1 hs)

/-- Second derivative: two logarithmic insertions, with positive sign. -/
theorem iteratedDeriv_two_riemannZeta_eq_logSqMomentLSeries {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv 2 riemannZeta s =
      LSeries (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))) s := by
  simpa [Function.iterate_succ_apply] using
    (iteratedDeriv_riemannZeta_eq_logMomentLSeries 2 hs)

/-- Third derivative: three logarithmic insertions, with the expected negative sign. -/
theorem iteratedDeriv_three_riemannZeta_eq_neg_logCubeMomentLSeries {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv 3 riemannZeta s =
      -LSeries
        (LSeries.logMul
          (LSeries.logMul
            (LSeries.logMul (fun _ : ℕ => (1 : ℂ))))) s := by
  rw [iteratedDeriv_riemannZeta_eq_logMomentLSeries 3 hs]
  norm_num [Function.iterate_succ_apply]

/-- Fourth derivative: four logarithmic insertions, with positive sign.  This is
the raw fourth-moment input for the next genuine Gibbs cumulant
`κ₄ = μ₄ - 3 μ₂²`. -/
theorem iteratedDeriv_four_riemannZeta_eq_logFourthMomentLSeries
    {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv 4 riemannZeta s =
      LSeries
        (LSeries.logMul
          (LSeries.logMul
            (LSeries.logMul
              (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))))) s := by
  rw [iteratedDeriv_riemannZeta_eq_logMomentLSeries 4 hs]
  norm_num [Function.iterate_succ_apply]

end GppZetaGibbsMoments

#print axioms GppZetaGibbsMoments.riemannZeta_eq_LSeries_one
#print axioms GppZetaGibbsMoments.iteratedDeriv_riemannZeta_eq_logMomentLSeries
#print axioms GppZetaGibbsMoments.deriv_riemannZeta_eq_neg_logMomentLSeries
#print axioms GppZetaGibbsMoments.iteratedDeriv_two_riemannZeta_eq_logSqMomentLSeries
#print axioms GppZetaGibbsMoments.iteratedDeriv_three_riemannZeta_eq_neg_logCubeMomentLSeries
#print axioms GppZetaGibbsMoments.iteratedDeriv_four_riemannZeta_eq_logFourthMomentLSeries
