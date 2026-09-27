import GppVerify.CelestialHolography.RegulatedBoxDilogSignedZeroContinuity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-!
# Negative endpoint continuity of the real dilogarithm series

The same Basel majorant that controls the positive endpoint controls the full interval
`[-1,1]`.  Hence the project's real dilogarithm series is continuous at `-1` from
inside that interval.  This supplies the endpoint bridge needed to extract
`Li2(-1) = -pi^2/12` from the real Landen identity.
-/

namespace GppRegulatedBoxDilogNegativeEndpointContinuity

open Set Filter
open scoped Topology
open GppRegulatedBoxDilogSeries
open GppRegulatedBoxSpenceConstant

/-- The real dilogarithm series tends to its series value at `-1` from `[-1,1]`. -/
theorem li2Series_tendsto_neg_one_within :
    Tendsto li2Series (𝓝[Icc (-1 : ℝ) 1] (-1)) (𝓝 (li2Series (-1))) := by
  unfold li2Series
  let bound : ℕ → ℝ := fun n => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)
  let term : ℝ → ℕ → ℝ := fun x n =>
    x ^ (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2)
  have hsum : Summable bound := by
    simpa [bound] using hasSum_shifted_recip_sq.summable
  have hterm : ∀ n : ℕ,
      Tendsto (fun x : ℝ => term x n) (𝓝[Icc (-1 : ℝ) 1] (-1))
        (𝓝 (term (-1) n)) := by
    intro n
    have hcont : ContinuousAt (fun x : ℝ => term x n) (-1) := by
      dsimp [term]
      fun_prop
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hbound : ∀ᶠ x in 𝓝[Icc (-1 : ℝ) 1] (-1), ∀ n : ℕ,
      ‖term x n‖ ≤ bound n := by
    filter_upwards [self_mem_nhdsWithin] with x hx n
    have hxabs : |x| ≤ 1 := by
      rw [abs_le]
      exact ⟨hx.1, hx.2⟩
    have hpow : |x| ^ (n + 1) ≤ 1 := by
      exact pow_le_one₀ (abs_nonneg x) hxabs
    have hden : 0 < (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
    dsimp [term, bound]
    rw [abs_div, abs_pow, abs_of_pos hden]
    exact (div_le_div_iff_of_pos_right hden).2 hpow
  have H := tendsto_tsum_of_dominated_convergence hsum hterm hbound
  simpa [term, bound] using H

end GppRegulatedBoxDilogNegativeEndpointContinuity

#print axioms GppRegulatedBoxDilogNegativeEndpointContinuity.li2Series_tendsto_neg_one_within
