import GppVerify.RiemannHypothesis.PadicZetaIntegral

/-!
# The p-adic "shell" measure

Real infrastructure continuing the p-adic zeta integral thread (Tate's-thesis lecture
notes, Example 4.10): the Haar measure of the "shell" `pⁿ ℤ_p \ pⁿ⁺¹ ℤ_p` (the set of
`x` with `‖x‖ = p⁻ⁿ` exactly) is `p⁻ⁿ(1 - 1/p) = p⁻ⁿ - p⁻⁽ⁿ⁺¹⁾`. This is the term-by-term
building block for the geometric-series evaluation of `∫_{ℤ_p} ‖x‖^s dμ`. Not sourced
from a specific Golden Physics Project paper.
-/

namespace GppPadicShell

open MeasureTheory
open scoped ENNReal

variable (p : ℕ) [Fact p.Prime]

/-- `pⁿ ℤ_p` (as a set) is a closed ball, hence measurable. -/
theorem measurableSet_span_pow (n : ℕ) :
    MeasurableSet (Ideal.span {(p : PadicInt p) ^ n} : Set (PadicInt p)) := by
  have heq : (Ideal.span {(p : PadicInt p) ^ n} : Set (PadicInt p)) =
      Metric.closedBall 0 ((p : ℝ) ^ (-(n : ℤ))) := by
    ext x
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm
  rw [heq]
  exact Metric.isClosed_closedBall.measurableSet

/-- **Shell measure**: the set of `x` with `‖x‖ = p⁻ⁿ` exactly (the "shell"
    `pⁿ ℤ_p \ pⁿ⁺¹ ℤ_p`) has Haar measure `p⁻ⁿ - p⁻⁽ⁿ⁺¹⁾`. -/
theorem haarMeasure_shell (n : ℕ) :
    GppPadicHaar.haarMeasure p
        ((Ideal.span {(p : PadicInt p) ^ n} : Set (PadicInt p)) \
          (Ideal.span {(p : PadicInt p) ^ (n + 1)} : Set (PadicInt p))) =
      ((p : ℝ≥0∞) ^ n)⁻¹ - ((p : ℝ≥0∞) ^ (n + 1))⁻¹ := by
  have hsub : (Ideal.span {(p : PadicInt p) ^ (n + 1)} : Set (PadicInt p)) ⊆
      (Ideal.span {(p : PadicInt p) ^ n} : Set (PadicInt p)) :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (p : PadicInt p) (Nat.le_succ n))
  have hmeasB : MeasurableSet (Ideal.span {(p : PadicInt p) ^ (n + 1)} : Set (PadicInt p)) :=
    measurableSet_span_pow p (n + 1)
  have hpne : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).pos.ne'
  have hfin : GppPadicHaar.haarMeasure p
      (Ideal.span {(p : PadicInt p) ^ (n + 1)} : Set (PadicInt p)) ≠ ⊤ := by
    rw [GppPadicZetaIntegral.haarMeasure_span_pow]
    exact ENNReal.inv_ne_top.mpr (pow_ne_zero (n + 1) hpne)
  rw [measure_diff hsub hmeasB.nullMeasurableSet hfin, GppPadicZetaIntegral.haarMeasure_span_pow,
      GppPadicZetaIntegral.haarMeasure_span_pow]

end GppPadicShell
