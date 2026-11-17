import GppVerify.RiemannHypothesis.BoxArchimedean
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# A positive series for `Gcl`, with partial-sum and tail bounds

With `u = e^{−t/2} ∈ (0, 1)`, the `log` and `arctan` series combine so that the odd-`k` terms cancel:

`Gcl t = Σ_k (1 + (−1)^k) u^{2k+1}/(2k+1) = Σ_j 2 u^{4j+1}/(4j+1)`.

Every term is `≥ 0`, so

* `Gcl_ge_partial`: any partial sum is a rigorous lower bound (no tail estimate needed);
* `Gcl_le_partial_add_tail`: `Gcl t ≤ Σ_{k<K} (1 + (−1)^k) u^{2k+1}/(2k+1) + 2u^{2K+1}/(1 − u²)`.

This is the analytic input for the first-interval numerics (`BoxInitialInterval.lean`); nothing here is a statement
about positivity of the Weil form.

No `sorry`, no axiom.
-/

open Real Set Filter Topology

noncomputable section

namespace GppGclSeries

open GppBoxCurvature

/-- The term of the combined series. -/
def gterm (u : ℝ) (k : ℕ) : ℝ := (1 + (-1 : ℝ) ^ k) * u ^ (2 * k + 1) / (2 * k + 1)

theorem gterm_nonneg {u : ℝ} (hu : 0 ≤ u) (k : ℕ) : 0 ≤ gterm u k := by
  unfold gterm
  have h : 0 ≤ 1 + (-1 : ℝ) ^ k := by
    rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h] <;> norm_num
  positivity

theorem gterm_le {u : ℝ} (hu : 0 ≤ u) (k : ℕ) : gterm u k ≤ 2 * u ^ (2 * k + 1) := by
  unfold gterm
  have h : 1 + (-1 : ℝ) ^ k ≤ 2 := by
    rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h] <;> norm_num
  have h0 : 0 ≤ 1 + (-1 : ℝ) ^ k := by
    rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h] <;> norm_num
  have hp : 0 ≤ u ^ (2 * k + 1) := by positivity
  have hd : (1 : ℝ) ≤ 2 * k + 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right h hp, mul_nonneg hp (show (0 : ℝ) ≤ 2 * k from by positivity)]

/-- The combined series sums to `Gcl`. -/
theorem Gcl_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (gterm (Real.exp (-t / 2))) (Gcl t) := by
  have hu1 : Real.exp (-t / 2) < 1 := exp_neg_half_lt_one ht
  have hu0 : 0 < Real.exp (-t / 2) := Real.exp_pos _
  set u := Real.exp (-t / 2) with hu
  have habs : |u| < 1 := by rw [abs_of_pos hu0]; exact hu1
  have hnorm : ‖u‖ < 1 := by simpa using habs
  have hlog := (Real.hasSum_log_sub_log_of_abs_lt_one habs).mul_left (1 / 2)
  have harc := Real.hasSum_arctan hnorm
  have hs := hlog.add harc
  have hG : Gcl t = 1 / 2 * (Real.log (1 + u) - Real.log (1 - u)) + Real.arctan u := by
    unfold Gcl
    rw [Real.log_div (by linarith) (by linarith)]
  rw [hG]
  have e : gterm u = fun b : ℕ => 1 / 2 * (2 * (1 / (2 * (b : ℝ) + 1)) * u ^ (2 * b + 1)) +
      (-1) ^ b * u ^ (2 * b + 1) / ((2 * b + 1 : ℕ) : ℝ) := by
    funext k
    unfold gterm
    push_cast
    ring
  rw [e]
  exact hs

theorem Gcl_ge_partial {t : ℝ} (ht : 0 < t) (K : ℕ) :
    ∑ k ∈ Finset.range K, gterm (Real.exp (-t / 2)) k ≤ Gcl t :=
  sum_le_hasSum _ (fun k _ => gterm_nonneg (Real.exp_pos _).le k) (Gcl_hasSum ht)

theorem Gcl_le_partial_add_tail {t : ℝ} (ht : 0 < t) (K : ℕ) :
    Gcl t ≤ ∑ k ∈ Finset.range K, gterm (Real.exp (-t / 2)) k +
      2 * Real.exp (-t / 2) ^ (2 * K + 1) / (1 - Real.exp (-t / 2) ^ 2) := by
  have hu1 : Real.exp (-t / 2) < 1 := exp_neg_half_lt_one ht
  have hu0 : 0 < Real.exp (-t / 2) := Real.exp_pos _
  set u := Real.exp (-t / 2) with hu
  have hs := (Gcl_hasSum ht).summable
  have hsplit := hs.sum_add_tsum_nat_add K
  rw [(Gcl_hasSum ht).tsum_eq] at hsplit
  have hq : u ^ 2 < 1 := by nlinarith
  have hgeo : HasSum (fun k : ℕ => 2 * u ^ (2 * (k + K) + 1))
      (2 * u ^ (2 * K + 1) / (1 - u ^ 2)) := by
    have h0 : HasSum (fun k : ℕ => (u ^ 2) ^ k) (1 - u ^ 2)⁻¹ :=
      hasSum_geometric_of_lt_one (by positivity) hq
    have h1 := h0.mul_left (2 * u ^ (2 * K + 1))
    have e : (fun k : ℕ => 2 * u ^ (2 * (k + K) + 1)) =
        fun k : ℕ => 2 * u ^ (2 * K + 1) * (u ^ 2) ^ k := by
      funext k
      rw [show 2 * (k + K) + 1 = 2 * k + (2 * K + 1) by ring, pow_add, pow_mul]
      ring
    rw [e, div_eq_mul_inv]
    exact h1
  have hle : ∑' k, gterm u (k + K) ≤ 2 * u ^ (2 * K + 1) / (1 - u ^ 2) := by
    rw [← hgeo.tsum_eq]
    exact (summable_nat_add_iff K).mpr hs |>.tsum_le_tsum
      (fun k => gterm_le hu0.le (k + K)) hgeo.summable
  linarith

end GppGclSeries

#print axioms GppGclSeries.Gcl_ge_partial
#print axioms GppGclSeries.Gcl_le_partial_add_tail
