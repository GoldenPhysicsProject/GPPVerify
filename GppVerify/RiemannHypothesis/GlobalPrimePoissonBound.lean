import GppVerify.RiemannHypothesis.GlobalPrimePoissonPositiveType
import GppVerify.RiemannHypothesis.PositiveTypeEvenBound
import Mathlib.Tactic

/-!
# Pointwise bound for the global prime-Poisson / zeta response

The certified global prime-Poisson response is positive type for every `a > 1`.
It is also even, since each local Poisson kernel depends on the spectral variable
through `cos(t log p)`. Therefore the standard 2-by-2 positive-type bound gives
an exact pointwise domination by the zero-frequency response.
-/

namespace GppGlobalPrimePoissonBound

open GppPrimePoissonRadial
open GppCutkoskyWeil
open GppVonMangoldtPrimePowerPoissonFiber
open GppGlobalPrimePoissonPositiveType
open GppPositiveTypeEvenBound

/-- Every local arbitrary-radial prime Poisson response is even in `t`. -/
theorem WpA_neg (p a t : ℝ) : WpA p a (-t) = WpA p a t := by
  unfold WpA KrClosed
  rw [show (-t) * Real.log p = -(t * Real.log p) by ring, Real.cos_neg]

/-- The countable global prime-Poisson sum is even. -/
theorem tsum_WpA_neg {a : ℝ} (t : ℝ) :
    (∑' p : Nat.Primes, WpA ((p : ℕ) : ℝ) a (-t)) =
      ∑' p : Nat.Primes, WpA ((p : ℕ) : ℝ) a t := by
  apply tsum_congr
  intro p
  exact WpA_neg ((p : ℕ) : ℝ) a t

/-- The doubled real logarithmic-derivative response is even on `a > 1`. -/
theorem zetaResponse_even {a : ℝ} (ha : 1 < a) (t : ℝ) :
    2 * (-(Complex.deriv Complex.riemannZeta
      ((a : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) /
      Complex.riemannZeta ((a : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))).re =
    2 * (-(Complex.deriv Complex.riemannZeta
      ((a : ℂ) + (t : ℂ) * Complex.I) /
      Complex.riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I))).re := by
  rw [two_mul_neg_zeta_logDeriv_re_eq_tsum_WpA ha,
    two_mul_neg_zeta_logDeriv_re_eq_tsum_WpA ha]
  exact tsum_WpA_neg t

/-- **Half-plane zeta-response bound from positive type.** For every `a > 1`, the
absolute value of the doubled real logarithmic derivative at height `t` is bounded
by its value on the positive real axis. -/
theorem abs_zetaResponse_le_zero {a : ℝ} (ha : 1 < a) (t : ℝ) :
    |2 * (-(Complex.deriv Complex.riemannZeta
      ((a : ℂ) + (t : ℂ) * Complex.I) /
      Complex.riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I))).re| ≤
    2 * (-(Complex.deriv Complex.riemannZeta (a : ℂ) /
      Complex.riemannZeta (a : ℂ))).re := by
  let P : ℝ → ℝ := fun u =>
    2 * (-(Complex.deriv Complex.riemannZeta
      ((a : ℂ) + (u : ℂ) * Complex.I) /
      Complex.riemannZeta ((a : ℂ) + (u : ℂ) * Complex.I))).re
  have hP : GppHaarPositivityWeil.PositiveType P := by
    simpa [P] using neg_zeta_logDeriv_response_positiveType ha
  have heven : ∀ u : ℝ, P (-u) = P u := by
    intro u
    simpa [P] using zetaResponse_even ha u
  have h := abs_le_at_zero_of_even_positiveType hP heven t
  simpa [P] using h

/-- **Undoubled form.** The real part of the logarithmic derivative at height `t`
is bounded in absolute value by its positive-real-axis value. -/
theorem abs_neg_zeta_logDeriv_re_le_real_axis {a : ℝ} (ha : 1 < a) (t : ℝ) :
    |(-(Complex.deriv Complex.riemannZeta
      ((a : ℂ) + (t : ℂ) * Complex.I) /
      Complex.riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I))).re| ≤
    (-(Complex.deriv Complex.riemannZeta (a : ℂ) /
      Complex.riemannZeta (a : ℂ))).re := by
  have h := abs_zetaResponse_le_zero ha t
  rw [abs_mul] at h
  norm_num at h
  linarith

end GppGlobalPrimePoissonBound

#print axioms GppGlobalPrimePoissonBound.abs_zetaResponse_le_zero
#print axioms GppGlobalPrimePoissonBound.abs_neg_zeta_logDeriv_re_le_real_axis
