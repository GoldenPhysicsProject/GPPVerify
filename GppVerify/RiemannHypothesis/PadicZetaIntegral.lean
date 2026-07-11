import GppVerify.RiemannHypothesis.HaarSubgroupIndex
import GppVerify.RiemannHypothesis.PadicHaarMeasure
import GppVerify.RiemannHypothesis.PadicIndexPn

/-!
# The Haar measure of `pⁿ ℤ_p`

The payoff of `HaarSubgroupIndex.lean` + `PadicHaarMeasure.lean` + `PadicIndexPn.lean`: the
p-adic integral formula from Tate's-thesis lecture notes (Example 4.10), `μ(pⁿ ℤ_p) = p⁻ⁿ`.
Not sourced from a specific Golden Physics Project paper.
-/

namespace GppPadicZetaIntegral

open MeasureTheory
open scoped ENNReal

variable (p : ℕ) [Fact p.Prime]

/-- **The Haar measure of `pⁿ ℤ_p` is `p⁻ⁿ`.** -/
theorem haarMeasure_span_pow (n : ℕ) :
    GppPadicHaar.haarMeasure p (Ideal.span {(p : PadicInt p) ^ n} : Set (PadicInt p)) =
      ((p : ℝ≥0∞) ^ n)⁻¹ := by
  set H : AddSubgroup (PadicInt p) := (Ideal.span {(p : PadicInt p) ^ n}).toAddSubgroup with hHdef
  have hset_eq : (Ideal.span {(p : PadicInt p) ^ n} : Set (PadicInt p)) = (H : Set (PadicInt p)) :=
    rfl
  rw [hset_eq]
  have hcard : Nat.card (PadicInt p ⧸ H) = p ^ n := GppPadicIndex.card_quotient_span_pow p n
  haveI hfin : Finite (PadicInt p ⧸ H) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact pow_ne_zero n (Fact.out : p.Prime).pos.ne'
  have hclosed : IsClosed ((H : Set (PadicInt p))) := by
    have heq : (H : Set (PadicInt p)) = Metric.closedBall 0 ((p : ℝ) ^ (-(n : ℤ))) := by
      ext x
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm
    rw [heq]
    exact Metric.isClosed_closedBall
  have hmeas : MeasurableSet (H : Set (PadicInt p)) := hclosed.measurableSet
  have hkey := GppHaarSubgroupIndex.index_vadd_measure_eq_univ (GppPadicHaar.haarMeasure p) H hmeas
  rw [hcard, GppPadicHaar.haarMeasure_univ] at hkey
  have hp0 : ((p : ℝ≥0∞) ^ n) ≠ 0 := by positivity
  have hptop : ((p : ℝ≥0∞) ^ n) ≠ ⊤ := by
    exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)
  have hmul : ((p : ℝ≥0∞) ^ n) * GppPadicHaar.haarMeasure p (H : Set (PadicInt p)) = 1 := by
    rw [← hkey]
    simp [nsmul_eq_mul]
  calc GppPadicHaar.haarMeasure p (H : Set (PadicInt p))
      = ((p : ℝ≥0∞) ^ n)⁻¹ * (((p : ℝ≥0∞) ^ n) * GppPadicHaar.haarMeasure p (H : Set (PadicInt p))) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hp0 hptop, one_mul]
    _ = ((p : ℝ≥0∞) ^ n)⁻¹ * 1 := by rw [hmul]
    _ = ((p : ℝ≥0∞) ^ n)⁻¹ := mul_one _

end GppPadicZetaIntegral
