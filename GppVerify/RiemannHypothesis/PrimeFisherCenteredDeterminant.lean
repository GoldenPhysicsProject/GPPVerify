import GppVerify.RiemannHypothesis.PrimeFisherCenteredGeometry
import GppVerify.RiemannHypothesis.PrimeHankelPolynomialSummability
import GppVerify.RiemannHypothesis.StrictQuadraticDeterminant
import Mathlib.Tactic

/-!
# Strict determinant of the centered countable prime-Fisher geometry

The centered two-observable prime-Fisher score is already known to have strictly
positive probability-normalized mean square for every nonzero coefficient pair.
This file identifies that `tsum` exactly with the covariance quadratic form and
then applies the abstract strict-quadratic determinant theorem.

No finite truncation or countable Cauchy--Binet argument is used.
-/

namespace GppPrimeFisherCenteredDeterminant

open Polynomial
open GppPrimeFisherProbability
open GppPrimeFisherCenteredGeometry
open GppPrimeHankelFisherSpecialization
open GppPrimeFisherMomentSummability
open GppPrimeHankelPolynomialSummability
open GppStrictQuadraticDeterminant

/-- Centered logarithmic observable. -/
noncomputable def centeredLog (beta : ℝ) (n : ℕ) : ℝ :=
  Real.log n - meanLog beta

/-- Centered squared-logarithmic observable. -/
noncomputable def centeredLogSq (beta : ℝ) (n : ℕ) : ℝ :=
  (Real.log n) ^ 2 - meanLogSq beta

/-- Variance of `log n` under the normalized prime-Fisher measure. -/
noncomputable def centeredLogVariance (beta : ℝ) : ℝ :=
  primeFisherExpectation beta (fun n : ℕ => (centeredLog beta n) ^ 2)

/-- Covariance of `log n` and `(log n)^2`. -/
noncomputable def centeredLogSquareCovariance (beta : ℝ) : ℝ :=
  primeFisherExpectation beta
    (fun n : ℕ => centeredLog beta n * centeredLogSq beta n)

/-- Variance of `(log n)^2`. -/
noncomputable def centeredLogSquareVariance (beta : ℝ) : ℝ :=
  primeFisherExpectation beta (fun n : ℕ => (centeredLogSq beta n) ^ 2)

/-- Determinant of the normalized covariance matrix of `log n` and `(log n)^2`. -/
noncomputable def centeredFisherDet (beta : ℝ) : ℝ :=
  centeredLogVariance beta * centeredLogSquareVariance beta -
    (centeredLogSquareCovariance beta) ^ 2

private theorem summable_prob_centeredLog_sq
    {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ =>
      primeFisherProbability beta n * (centeredLog beta n) ^ 2) := by
  let p : ℝ[X] := X - C (meanLog beta)
  have h := summable_fisherWeight_mul_polynomial_eval_sq hbeta p
  have hdiv := h.div_const (primeFisherMass beta)
  refine hdiv.congr ?_
  intro n
  unfold primeFisherProbability centeredLog
  simp [p]

private theorem summable_prob_centeredLogSq_sq
    {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ =>
      primeFisherProbability beta n * (centeredLogSq beta n) ^ 2) := by
  let p : ℝ[X] := X ^ 2 - C (meanLogSq beta)
  have h := summable_fisherWeight_mul_polynomial_eval_sq hbeta p
  have hdiv := h.div_const (primeFisherMass beta)
  refine hdiv.congr ?_
  intro n
  unfold primeFisherProbability centeredLogSq
  simp [p]

private theorem summable_prob_centered_cross
    {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ =>
      primeFisherProbability beta n *
        (centeredLog beta n * centeredLogSq beta n)) := by
  let p : ℝ[X] :=
    (X - C (meanLog beta)) * (X ^ 2 - C (meanLogSq beta))
  have h : Summable (fun n : ℕ => fisherWeight beta n * p.eval (Real.log n)) := by
    apply summable_weight_mul_polynomial_eval
    intro r
    exact summable_fisherWeight_mul_log_pow r hbeta
  have hdiv := h.div_const (primeFisherMass beta)
  refine hdiv.congr ?_
  intro n
  unfold primeFisherProbability centeredLog centeredLogSq
  simp [p]
  ring

/-- Exact coefficient identification for the centered prime-Fisher score. -/
theorem normalized_centered_quadratic_eq_covariance
    {beta a b : ℝ} (hbeta : 1 < beta) :
    (∑' n : ℕ, primeFisherProbability beta n *
      (a * centeredLog beta n + b * centeredLogSq beta n) ^ 2) =
      centeredLogVariance beta * a ^ 2 +
        2 * centeredLogSquareCovariance beta * a * b +
        centeredLogSquareVariance beta * b ^ 2 := by
  have hA := summable_prob_centeredLog_sq hbeta
  have hB := summable_prob_centered_cross hbeta
  have hC := summable_prob_centeredLogSq_sq hbeta
  have hAa : Summable (fun n : ℕ =>
      a ^ 2 * (primeFisherProbability beta n * (centeredLog beta n) ^ 2)) :=
    hA.mul_left (a ^ 2)
  have hBb : Summable (fun n : ℕ =>
      (2 * a * b) *
        (primeFisherProbability beta n *
          (centeredLog beta n * centeredLogSq beta n))) :=
    hB.mul_left (2 * a * b)
  have hCc : Summable (fun n : ℕ =>
      b ^ 2 * (primeFisherProbability beta n * (centeredLogSq beta n) ^ 2)) :=
    hC.mul_left (b ^ 2)
  calc
    (∑' n : ℕ, primeFisherProbability beta n *
      (a * centeredLog beta n + b * centeredLogSq beta n) ^ 2) =
        ∑' n : ℕ,
          a ^ 2 * (primeFisherProbability beta n * (centeredLog beta n) ^ 2) +
          (2 * a * b) *
            (primeFisherProbability beta n *
              (centeredLog beta n * centeredLogSq beta n)) +
          b ^ 2 *
            (primeFisherProbability beta n * (centeredLogSq beta n) ^ 2) := by
              apply tsum_congr
              intro n
              ring
    _ =
        a ^ 2 * (∑' n : ℕ,
          primeFisherProbability beta n * (centeredLog beta n) ^ 2) +
        (2 * a * b) * (∑' n : ℕ,
          primeFisherProbability beta n *
            (centeredLog beta n * centeredLogSq beta n)) +
        b ^ 2 * (∑' n : ℕ,
          primeFisherProbability beta n * (centeredLogSq beta n) ^ 2) := by
            rw [tsum_add (hAa.add hBb) hCc, tsum_add hAa hBb]
            simp only [tsum_mul_left]
    _ =
      centeredLogVariance beta * a ^ 2 +
        2 * centeredLogSquareCovariance beta * a * b +
        centeredLogSquareVariance beta * b ^ 2 := by
          unfold centeredLogVariance centeredLogSquareCovariance centeredLogSquareVariance
          unfold primeFisherExpectation
          ring

/-- **Strict countable two-observable prime-Fisher determinant.**  For every
`beta > 1`, the covariance matrix of the centered observables `log n` and
`(log n)^2` is positive definite. -/
theorem centeredFisherDet_pos {beta : ℝ} (hbeta : 1 < beta) :
    0 < centeredFisherDet beta := by
  have hpos : ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 →
      0 < centeredLogVariance beta * a ^ 2 +
        2 * centeredLogSquareCovariance beta * a * b +
        centeredLogSquareVariance beta * b ^ 2 := by
    intro a b hab
    rw [← normalized_centered_quadratic_eq_covariance hbeta]
    simpa [centeredLog, centeredLogSq] using
      (normalized_centered_quadratic_pos (beta := beta) (a := a) (b := b) hbeta hab)
  unfold centeredFisherDet
  exact det_pos_of_quadratic_pos
    (centeredLogVariance beta)
    (centeredLogSquareCovariance beta)
    (centeredLogSquareVariance beta) hpos

end GppPrimeFisherCenteredDeterminant

#print axioms GppPrimeFisherCenteredDeterminant.normalized_centered_quadratic_eq_covariance
#print axioms GppPrimeFisherCenteredDeterminant.centeredFisherDet_pos
