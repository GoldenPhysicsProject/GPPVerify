import GppVerify.RiemannHypothesis.WeightedVarianceFinite
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Countable weighted variance positivity

This file passes the finite weighted Cauchy--Schwarz inequality to an infinite
`ℕ`-indexed summable family.  It is the abstract analytic bridge needed before
specializing to the zeta Gibbs weights.
-/

namespace GppWeightedVarianceInfinite

open Filter
open scoped BigOperators Topology

/-- The unnormalized variance numerator stays nonnegative under an `ℕ`-indexed
summable limit. -/
theorem weighted_variance_numerator_nonneg_tsum
    (w x : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n)
    (hW : Summable w)
    (hM : Summable (fun n => w n * x n))
    (hQ : Summable (fun n => w n * x n ^ 2)) :
    0 ≤ (∑' n, w n) * (∑' n, w n * x n ^ 2) -
      (∑' n, w n * x n) ^ 2 := by
  have hpartial : ∀ N : ℕ,
      0 ≤ (∑ n ∈ Finset.range N, w n) *
          (∑ n ∈ Finset.range N, w n * x n ^ 2) -
          (∑ n ∈ Finset.range N, w n * x n) ^ 2 := by
    intro N
    exact GppWeightedVarianceFinite.weighted_variance_numerator_nonneg
      (Finset.range N) w x (by
        intro n hn
        exact hw n)
  have hWlim : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, w n) atTop
      (𝓝 (∑' n, w n)) := hW.hasSum.tendsto_sum_nat
  have hMlim : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, w n * x n) atTop
      (𝓝 (∑' n, w n * x n)) := hM.hasSum.tendsto_sum_nat
  have hQlim : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, w n * x n ^ 2) atTop
      (𝓝 (∑' n, w n * x n ^ 2)) := hQ.hasSum.tendsto_sum_nat
  have hlim : Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.range N, w n) *
            (∑ n ∈ Finset.range N, w n * x n ^ 2) -
          (∑ n ∈ Finset.range N, w n * x n) ^ 2)
      atTop
      (𝓝 ((∑' n, w n) * (∑' n, w n * x n ^ 2) -
        (∑' n, w n * x n) ^ 2)) :=
    (hWlim.mul hQlim).sub (hMlim.pow 2)
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall hpartial)

/-- After division by a positive total weight, the normalized countable weighted
variance is nonnegative. -/
theorem normalized_weighted_variance_nonneg_tsum
    (w x : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n)
    (hW : Summable w)
    (hM : Summable (fun n => w n * x n))
    (hQ : Summable (fun n => w n * x n ^ 2))
    (hWpos : 0 < ∑' n, w n) :
    0 ≤ (∑' n, w n * x n ^ 2) / (∑' n, w n) -
      ((∑' n, w n * x n) / (∑' n, w n)) ^ 2 := by
  have hnum := weighted_variance_numerator_nonneg_tsum w x hw hW hM hQ
  have hWne : (∑' n, w n) ≠ 0 := ne_of_gt hWpos
  rw [show
      (∑' n, w n * x n ^ 2) / (∑' n, w n) -
          ((∑' n, w n * x n) / (∑' n, w n)) ^ 2 =
        ((∑' n, w n) * (∑' n, w n * x n ^ 2) -
          (∑' n, w n * x n) ^ 2) / (∑' n, w n) ^ 2 by
        field_simp [hWne]
        ring]
  exact div_nonneg hnum (sq_nonneg _)

end GppWeightedVarianceInfinite

#print axioms GppWeightedVarianceInfinite.weighted_variance_numerator_nonneg_tsum
#print axioms GppWeightedVarianceInfinite.normalized_weighted_variance_nonneg_tsum
