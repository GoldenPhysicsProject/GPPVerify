import GppVerify.CelestialHolography.RegulatedBoxDilogSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
# Endpoint constant for the real Spence identity

The local dilogarithm series satisfies

  Li₂(1) = sum_{m>=1} 1/m² = π²/6.

This isolates the exact constant needed after the previously formalized derivative
cancellation of the Spence combination.
-/

namespace GppRegulatedBoxSpenceConstant

open GppRegulatedBoxDilogSeries

/-- The shifted reciprocal-square series has the classical Basel sum. -/
theorem hasSum_shifted_recip_sq :
    HasSum
      (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2))
      (Real.pi ^ 2 / 6) := by
  let f : ℕ → ℝ := fun n => (1 : ℝ) / ((n : ℝ) ^ 2)
  have hz : HasSum f (Real.pi ^ 2 / 6) := by
    simpa [f] using hasSum_zeta_two
  have hs : Summable f := hz.summable
  have hsTail : Summable (fun n : ℕ => f (n + 1)) :=
    (summable_nat_add_iff 1).2 hs
  have hsplit := hs.sum_add_tsum_nat_add 1
  have htail : (∑' n : ℕ, f (n + 1)) = Real.pi ^ 2 / 6 := by
    rw [hz.tsum_eq] at hsplit
    simpa [f] using hsplit
  have hHas : HasSum (fun n : ℕ => f (n + 1)) (Real.pi ^ 2 / 6) := by
    rw [← htail]
    exact hsTail.hasSum
  simpa [f] using hHas

/-- Exact endpoint value of the project's local real dilogarithm series. -/
theorem li2Series_one :
    li2Series 1 = Real.pi ^ 2 / 6 := by
  unfold li2Series
  simpa using hasSum_shifted_recip_sq.tsum_eq

end GppRegulatedBoxSpenceConstant

#print axioms GppRegulatedBoxSpenceConstant.li2Series_one
