import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Prime occupation threshold source and covariance

Source: Astra, GPP-bridge work/2026-10-28_astra_fock_occupation_sector_shadow.md.
For the geometric prime occupation law, occupation threshold N_p ≥ k has
probability x_p^k, hence the local source reproduces prime-power coefficients.
Centered thresholds have covariance x^(max k l) - x^(k+l).
This does not prove signed completed Weil positivity or RH.
-/

namespace GppPrimeThresholdSourceCovariance

def geometricMass (x : ℝ) (n : ℕ) : ℝ := (1 - x) * x ^ n

theorem finite_geometric_tail (x : ℝ) (k N : ℕ) :
    (1 - x) * (∑ j ∈ Finset.range N, x ^ (k + j)) = x ^ k - x ^ (k + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have h : k + (N + 1) = (k + N) + 1 := by omega
      rw [h, pow_succ]
      ring

theorem threshold_hasSum (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    HasSum (fun j : ℕ => geometricMass x (k + j)) (x ^ k) := by
  have h := (hasSum_geometric_of_lt_one hx0 hx1).mul_left ((1 - x) * x ^ k)
  have hx : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have heq : (fun j : ℕ => geometricMass x (k + j)) =
      (fun j : ℕ => (1 - x) * x ^ k * x ^ j) := by
    funext j
    simp only [geometricMass, pow_add]
    ring
  have hval : (1 - x) * x ^ k * (1 - x)⁻¹ = x ^ k := by
    calc
      (1 - x) * x ^ k * (1 - x)⁻¹ = ((1 - x) * (1 - x)⁻¹) * x ^ k := by ring
      _ = x ^ k := by simp [hx]
  rw [heq]
  rw [hval] at h
  exact h

theorem finite_source (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (S : Finset ℕ) (a : ℕ → ℝ) :
    (∑ k ∈ S, a k * x ^ k) =
      ∑ k ∈ S, a k * (∑' j : ℕ, geometricMass x (k + j)) := by
  apply Finset.sum_congr rfl
  intro k _
  rw [(threshold_hasSum x hx0 hx1 k).tsum_eq]

def thresholdCov (x : ℝ) (k l : ℕ) : ℝ := x ^ max k l - x ^ (k + l)

theorem covariance_symm (x : ℝ) (k l : ℕ) :
    thresholdCov x k l = thresholdCov x l k := by
  simp [thresholdCov, max_comm, add_comm]

theorem covariance_of_le (x : ℝ) (k l : ℕ) (hkl : k ≤ l) :
    thresholdCov x k l = x ^ l * (1 - x ^ k) := by
  simp only [thresholdCov, max_eq_right hkl, pow_add]
  ring

theorem covariance_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (k l : ℕ) : 0 ≤ thresholdCov x k l := by
  have hpow (j : ℕ) : x ^ j ≤ 1 := pow_le_one₀ hx0 hx1
  rcases le_total k l with hkl | hlk
  · rw [covariance_of_le x k l hkl]
    exact mul_nonneg (pow_nonneg hx0 _) (sub_nonneg.mpr (hpow k))
  · rw [covariance_symm, covariance_of_le x l k hlk]
    exact mul_nonneg (pow_nonneg hx0 _) (sub_nonneg.mpr (hpow l))

theorem covariance_diagonal (x : ℝ) (k : ℕ) :
    thresholdCov x k k = x ^ k * (1 - x ^ k) := by
  rw [covariance_of_le x k k le_rfl]

theorem covariance_two_minor (x : ℝ) (k l : ℕ) (hkl : k ≤ l) :
    thresholdCov x k k * thresholdCov x l l - thresholdCov x k l ^ 2 =
      x ^ (k + l) * (1 - x ^ k) * (1 - x ^ (l - k)) := by
  rw [covariance_diagonal, covariance_diagonal, covariance_of_le x k l hkl]
  have hpow : x ^ l = x ^ k * x ^ (l - k) := by
    conv_lhs => rw [show l = k + (l - k) by omega, pow_add]
  rw [pow_add, hpow]
  ring

theorem covariance_two_minor_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (k l : ℕ) :
    0 ≤ thresholdCov x k k * thresholdCov x l l - thresholdCov x k l ^ 2 := by
  have hpow (j : ℕ) : x ^ j ≤ 1 := pow_le_one₀ hx0 hx1
  rcases le_total k l with hkl | hlk
  · rw [covariance_two_minor x k l hkl]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hx0 _) (sub_nonneg.mpr (hpow k)))
      (sub_nonneg.mpr (hpow (l - k)))
  · rw [covariance_symm x k l, mul_comm (thresholdCov x k k) (thresholdCov x l l)]
    rw [covariance_two_minor x l k hlk]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hx0 _) (sub_nonneg.mpr (hpow l)))
      (sub_nonneg.mpr (hpow (k - l)))

end GppPrimeThresholdSourceCovariance

#print axioms GppPrimeThresholdSourceCovariance.finite_geometric_tail
#print axioms GppPrimeThresholdSourceCovariance.threshold_hasSum
#print axioms GppPrimeThresholdSourceCovariance.finite_source
#print axioms GppPrimeThresholdSourceCovariance.covariance_nonneg
#print axioms GppPrimeThresholdSourceCovariance.covariance_two_minor_nonneg
