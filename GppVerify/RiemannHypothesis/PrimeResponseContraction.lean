import GppVerify.RiemannHypothesis.GlobalPrimePoissonBound
import Mathlib.Tactic

/-!
# Normalized prime-response contraction

The global prime-Poisson response on `a > 1` is positive type, even, and bounded
in absolute value by its zero-frequency value.  This file converts that exact
bound into a concrete scalar contraction multiplier.  The chosen normalization
is in fact strictly contractive because its denominator contains the additional
positive unit term.  It does not identify the multiplier with the completed Weil
transfer map and makes no RH claim.
-/

namespace GppPrimeResponseContraction

open GppGlobalPrimePoissonBound

noncomputable def response (a t : ℝ) : ℝ :=
  2 * (-(Complex.deriv Complex.riemannZeta
    ((a : ℂ) + (t : ℂ) * Complex.I) /
    Complex.riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I))).re

/-- The zero-frequency response is nonnegative on the absolutely convergent half-plane. -/
theorem response_zero_nonneg {a : ℝ} (ha : 1 < a) :
    0 ≤ response a 0 := by
  have h := abs_zetaResponse_le_zero ha 0
  change |response a 0| ≤ response a 0 at h
  exact (abs_le_self_iff.mp h)

/-- A normalization that is always strictly positive in the denominator. -/
noncomputable def transfer (a t : ℝ) : ℝ :=
  response a t / (1 + response a 0)

/-- The normalized arithmetic response is a scalar contraction. -/
theorem abs_transfer_le_one {a : ℝ} (ha : 1 < a) (t : ℝ) :
    |transfer a t| ≤ 1 := by
  have h0 : 0 ≤ response a 0 := response_zero_nonneg ha
  have hden : 0 < 1 + response a 0 := by linarith
  have ht : |response a t| ≤ response a 0 := by
    simpa [response] using abs_zetaResponse_le_zero ha t
  unfold transfer
  rw [abs_div, abs_of_pos hden]
  exact (div_le_one hden).2 (le_trans ht (by linarith))

/-- The normalization is actually strictly contractive on `a > 1`: the prime
response is bounded by `response a 0`, whereas the denominator is the strictly
larger quantity `1 + response a 0`. -/
theorem abs_transfer_lt_one {a : ℝ} (ha : 1 < a) (t : ℝ) :
    |transfer a t| < 1 := by
  have h0 : 0 ≤ response a 0 := response_zero_nonneg ha
  have hden : 0 < 1 + response a 0 := by linarith
  have ht : |response a t| ≤ response a 0 := by
    simpa [response] using abs_zetaResponse_le_zero ha t
  unfold transfer
  rw [abs_div, abs_of_pos hden]
  apply lt_of_le_of_lt ((div_le_div_iff_of_pos_right hden).2 ht)
  exact (div_lt_one hden).2 (by linarith)

end GppPrimeResponseContraction

#print axioms GppPrimeResponseContraction.response_zero_nonneg
#print axioms GppPrimeResponseContraction.abs_transfer_le_one
#print axioms GppPrimeResponseContraction.abs_transfer_lt_one
