import GppVerify.RiemannHypothesis.GlobalPrimePoissonBound
import GppVerify.RiemannHypothesis.PositiveTypeSecondDifference
import Mathlib.Tactic

/-!
# Three-point inequality for the half-plane zeta response

For `a>1`, the real logarithmic-derivative response is, up to the harmless positive
factor two, the certified global prime-Poisson positive-type kernel. The generic
three-point Gram inequality therefore gives a discrete second-difference constraint.
-/

namespace GppGlobalPrimePoissonSecondDifference

open GppGlobalPrimePoissonPositiveType
open GppGlobalPrimePoissonBound
open GppPositiveTypeSecondDifference

/-- Real logarithmic-derivative response on the absolute-convergence half-plane. -/
noncomputable def zetaR (a t : ℝ) : ℝ :=
  (-(Complex.deriv Complex.riemannZeta
    ((a : ℂ) + (t : ℂ) * Complex.I) /
    Complex.riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I))).re

/-- **Arithmetic three-point positive-type inequality**:
`3 R_a(0) - 4 R_a(t) + R_a(2t) >= 0` for every `a>1`. -/
theorem zetaR_second_difference_nonneg {a : ℝ} (ha : 1 < a) (t : ℝ) :
    0 ≤ 3 * zetaR a 0 - 4 * zetaR a t + zetaR a (2 * t) := by
  let P : ℝ → ℝ := fun u => 2 * zetaR a u
  have hP : GppHaarPositivityWeil.PositiveType P := by
    simpa [P, zetaR] using neg_zeta_logDeriv_response_positiveType ha
  have heven : ∀ u : ℝ, P (-u) = P u := by
    intro u
    simpa [P, zetaR] using zetaResponse_even ha u
  have h := second_difference_lower_bound hP heven t
  dsimp [P] at h
  linarith

/-- Rearranged dyadic lower bound for the zeta response. -/
theorem zetaR_dyadic_lower_bound {a : ℝ} (ha : 1 < a) (t : ℝ) :
    4 * zetaR a t - 3 * zetaR a 0 ≤ zetaR a (2 * t) := by
  linarith [zetaR_second_difference_nonneg ha t]

end GppGlobalPrimePoissonSecondDifference

#print axioms GppGlobalPrimePoissonSecondDifference.zetaR_second_difference_nonneg
