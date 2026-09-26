import GppVerify.CelestialHolography.RegulatedBoxSpenceConstant
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-!
# Endpoint continuity of the local dilogarithm series

On the closed real interval `[0,1]`, every term

  x^(n+1) / (n+1)^2

is dominated by the summable Basel majorant `1/(n+1)^2`. Tannery's theorem therefore
permits endpoint limits to pass through the series. These are the endpoint bridges
needed to identify the constant in the real Spence identity.
-/

namespace GppRegulatedBoxDilogEndpointContinuity

open Set Filter
open scoped Topology
open GppRegulatedBoxDilogSeries
open GppRegulatedBoxSpenceConstant

/-- The project's local real dilogarithm series tends to its endpoint value as
`x -> 1` from inside `[0,1]`. -/
theorem li2Series_tendsto_one_within :
    Tendsto li2Series (𝓝[Icc (0 : ℝ) 1] 1) (𝓝 (li2Series 1)) := by
  unfold li2Series
  let bound : ℕ → ℝ := fun n => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)
  let term : ℝ → ℕ → ℝ := fun x n => x ^ (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2)
  have hsum : Summable bound := by
    simpa [bound] using hasSum_shifted_recip_sq.summable
  have hterm : ∀ n : ℕ,
      Tendsto (fun x : ℝ => term x n) (𝓝[Icc (0 : ℝ) 1] 1) (𝓝 (bound n)) := by
    intro n
    have hcont : ContinuousAt (fun x : ℝ => term x n) 1 := by
      dsimp [term]
      fun_prop
    have hlim :
        Tendsto (fun x : ℝ => term x n)
          (𝓝[Icc (0 : ℝ) 1] 1) (𝓝 (term 1 n)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa [term, bound] using hlim
  have hbound : ∀ᶠ x in 𝓝[Icc (0 : ℝ) 1] 1, ∀ n : ℕ,
      ‖term x n‖ ≤ bound n := by
    filter_upwards [self_mem_nhdsWithin] with x hx n
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hpow : x ^ (n + 1) ≤ 1 := pow_le_one₀ hx0 hx1
    have hden : 0 < (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
    dsimp [term, bound]
    rw [abs_of_nonneg (div_nonneg (pow_nonneg hx0 _) hden.le)]
    exact (div_le_div_iff_of_pos_right hden).2 hpow
  have H := tendsto_tsum_of_dominated_convergence hsum hterm hbound
  simpa [term, bound] using H

/-- The same dominated-convergence argument gives the zero endpoint exactly. -/
theorem li2Series_tendsto_zero_within :
    Tendsto li2Series (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0) := by
  unfold li2Series
  let bound : ℕ → ℝ := fun n => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)
  let term : ℝ → ℕ → ℝ := fun x n => x ^ (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2)
  have hsum : Summable bound := by
    simpa [bound] using hasSum_shifted_recip_sq.summable
  have hterm : ∀ n : ℕ,
      Tendsto (fun x : ℝ => term x n) (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0) := by
    intro n
    have hcont : ContinuousAt (fun x : ℝ => term x n) 0 := by
      dsimp [term]
      fun_prop
    have hlim :
        Tendsto (fun x : ℝ => term x n)
          (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 (term 0 n)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa [term] using hlim
  have hbound : ∀ᶠ x in 𝓝[Icc (0 : ℝ) 1] 0, ∀ n : ℕ,
      ‖term x n‖ ≤ bound n := by
    filter_upwards [self_mem_nhdsWithin] with x hx n
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hpow : x ^ (n + 1) ≤ 1 := pow_le_one₀ hx0 hx1
    have hden : 0 < (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
    dsimp [term, bound]
    rw [abs_of_nonneg (div_nonneg (pow_nonneg hx0 _) hden.le)]
    exact (div_le_div_iff_of_pos_right hden).2 hpow
  have H := tendsto_tsum_of_dominated_convergence hsum hterm hbound
  simpa [term] using H

/-- In particular, the unit-endpoint limit is the Basel constant. -/
theorem li2Series_tendsto_pi_sq_div_six :
    Tendsto li2Series (𝓝[Icc (0 : ℝ) 1] 1) (𝓝 (Real.pi ^ 2 / 6)) := by
  simpa [li2Series_one] using li2Series_tendsto_one_within

end GppRegulatedBoxDilogEndpointContinuity

#print axioms GppRegulatedBoxDilogEndpointContinuity.li2Series_tendsto_one_within
#print axioms GppRegulatedBoxDilogEndpointContinuity.li2Series_tendsto_zero_within
#print axioms GppRegulatedBoxDilogEndpointContinuity.li2Series_tendsto_pi_sq_div_six
