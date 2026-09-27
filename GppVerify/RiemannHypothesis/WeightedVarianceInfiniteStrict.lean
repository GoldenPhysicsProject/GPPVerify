import GppVerify.RiemannHypothesis.WeightedVarianceInfinite
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# Strict countable weighted variance from two distinct support points

A nonnegative summable weight has strictly positive normalized variance as soon as
two support points carry positive weight and the observable takes distinct values
there.  This is the abstract strictness mechanism needed by the zeta Gibbs gas,
and is independent of the von-Mangoldt/Fisher derivative chain.
-/

namespace GppWeightedVarianceInfiniteStrict

open scoped BigOperators

/-- A countable normalized weighted variance is strictly positive if two positive-weight
support points have distinct observable values. -/
theorem normalized_weighted_variance_pos_tsum
    (w x : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n)
    (hW : Summable w)
    (hM : Summable (fun n => w n * x n))
    (hQ : Summable (fun n => w n * x n ^ 2))
    (hWpos : 0 < ∑' n, w n)
    {i j : ℕ} (hwi : 0 < w i) (hwj : 0 < w j) (hxij : x i ≠ x j) :
    0 < (∑' n, w n * x n ^ 2) / (∑' n, w n) -
      ((∑' n, w n * x n) / (∑' n, w n)) ^ 2 := by
  let W : ℝ := ∑' n, w n
  let M : ℝ := ∑' n, w n * x n
  let μ : ℝ := M / W

  have hcenter : Summable (fun n => w n * (x n - μ) ^ 2) := by
    have hlin : Summable (fun n => (2 * μ) * (w n * x n)) := hM.mul_left _
    have hconst : Summable (fun n => μ ^ 2 * w n) := hW.mul_left _
    have hs := (hQ.sub hlin).add hconst
    exact hs.congr (fun n => by ring)

  have hcenter_nonneg : ∀ n, 0 ≤ w n * (x n - μ) ^ 2 := by
    intro n
    exact mul_nonneg (hw n) (sq_nonneg _)

  have hwitness : ∃ k : ℕ, 0 < w k * (x k - μ) ^ 2 := by
    by_cases hi : x i = μ
    · have hj : x j ≠ μ := by
        intro hjμ
        apply hxij
        calc
          x i = μ := hi
          _ = x j := hjμ.symm
      refine ⟨j, mul_pos hwj (sq_pos_of_ne_zero ?_)⟩
      exact sub_ne_zero.mpr hj
    · refine ⟨i, mul_pos hwi (sq_pos_of_ne_zero ?_)⟩
      exact sub_ne_zero.mpr hi

  have hTpos : 0 < ∑' n, w n * (x n - μ) ^ 2 := by
    obtain ⟨k, hk⟩ := hwitness
    exact hcenter.tsum_pos hcenter_nonneg k hk

  have hWne : W ≠ 0 := ne_of_gt hWpos
  have hTidentity :
      (∑' n, w n * (x n - μ) ^ 2) =
        (∑' n, w n * x n ^ 2) - 2 * μ * M + μ ^ 2 * W := by
    let a : ℕ → ℝ := fun n => w n * x n ^ 2
    let b : ℕ → ℝ := fun n => (2 * μ) * (w n * x n)
    let c : ℕ → ℝ := fun n => μ ^ 2 * w n
    have ha : Summable a := by simpa [a] using hQ
    have hb : Summable b := by
      simpa [b] using hM.mul_left (2 * μ)
    have hc : Summable c := by
      simpa [c] using hW.mul_left (μ ^ 2)
    have hab : Summable (fun n => a n - b n) := ha.sub hb
    have hterm : (fun n => w n * (x n - μ) ^ 2) =
        (fun n => (a n - b n) + c n) := by
      funext n
      dsimp [a, b, c]
      ring
    have hadd :
        tsum (fun n => (a n - b n) + c n) =
          tsum (fun n => a n - b n) + tsum c := hab.tsum_add hc
    have hsub :
        tsum (fun n => a n - b n) = tsum a - tsum b := ha.tsum_sub hb
    have hb_sum : tsum b = 2 * μ * M := by
      dsimp [b, M]
      simpa using hM.tsum_mul_left (2 * μ)
    have hc_sum : tsum c = μ ^ 2 * W := by
      dsimp [c, W]
      simpa using hW.tsum_mul_left (μ ^ 2)
    have ha_sum : tsum a = ∑' n, w n * x n ^ 2 := by
      rfl
    rw [show (∑' n, w n * (x n - μ) ^ 2) =
        tsum (fun n => (a n - b n) + c n) by rw [← hterm]]
    rw [hadd, hsub, ha_sum, hb_sum, hc_sum]

  have hvar_identity :
      (∑' n, w n * x n ^ 2) / W - (M / W) ^ 2 =
        (∑' n, w n * (x n - μ) ^ 2) / W := by
    rw [hTidentity]
    dsimp [μ]
    field_simp [hWne]
    ring

  rw [show (∑' n, w n) = W by rfl, show (∑' n, w n * x n) = M by rfl]
  rw [hvar_identity]
  exact div_pos hTpos hWpos

end GppWeightedVarianceInfiniteStrict

#print axioms GppWeightedVarianceInfiniteStrict.normalized_weighted_variance_pos_tsum
