import GppVerify.CelestialHolography.RegulatedBoxDilogEndpointContinuity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-!
# Signed zero-endpoint continuity of the real dilogarithm series

The endpoint theorem used in the positive Spence proof was stated within `[0,1]`.
For Landen and negative-axis inversion we also need to approach zero through negative
arguments.  The same Basel majorant works uniformly on the full signed interval
`[-1,1]`, because `|x|^(n+1) <= 1` there.
-/

namespace GppRegulatedBoxDilogSignedZeroContinuity

open Set Filter
open scoped Topology
open GppRegulatedBoxDilogSeries
open GppRegulatedBoxSpenceConstant

/-- The local real dilogarithm series tends to zero as `x -> 0` from anywhere in
`[-1,1]`. -/
theorem li2Series_tendsto_zero_signed :
    Tendsto li2Series (𝓝[Icc (-1 : ℝ) 1] 0) (𝓝 0) := by
  unfold li2Series
  let bound : ℕ → ℝ := fun n => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)
  let term : ℝ → ℕ → ℝ := fun x n =>
    x ^ (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2)
  have hsum : Summable bound := by
    simpa [bound] using hasSum_shifted_recip_sq.summable
  have hterm : ∀ n : ℕ,
      Tendsto (fun x : ℝ => term x n) (𝓝[Icc (-1 : ℝ) 1] 0) (𝓝 0) := by
    intro n
    have hcont : ContinuousAt (fun x : ℝ => term x n) 0 := by
      dsimp [term]
      fun_prop
    have hlim :
        Tendsto (fun x : ℝ => term x n)
          (𝓝[Icc (-1 : ℝ) 1] 0) (𝓝 (term 0 n)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa [term] using hlim
  have hbound : ∀ᶠ x in 𝓝[Icc (-1 : ℝ) 1] 0, ∀ n : ℕ,
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

end GppRegulatedBoxDilogSignedZeroContinuity

#print axioms GppRegulatedBoxDilogSignedZeroContinuity.li2Series_tendsto_zero_signed
