import GppVerify.RiemannHypothesis.PrimeThresholdSourceCovariance
import Mathlib.Tactic

/-!
# Prime threshold full finite Gram positivity

An arbitrary finite collection of geometric prime-occupation thresholds has a
positive covariance Gram form. No RH or Weil-sign hypothesis is used.
-/

namespace GppPrimeThresholdFullGram

open Finset

private def feature (x : ℝ) (k j : ℕ) : ℝ :=
  if j ≤ k then x ^ (k - j) else 0

private def weight (x : ℝ) (j : ℕ) : ℝ := (1 - x) * x ^ (j + 1)

/-- Causal innovation covariance, with threshold indices starting at one. -/
def innovationCov (x : ℝ) (N : ℕ) (k l : Fin N) : ℝ :=
  ∑ j : Fin N, weight x j.val * feature x k.val j.val * feature x l.val j.val

private theorem gram_algebra (N : ℕ) (a : Fin N → ℝ)
    (w : Fin N → ℝ) (f : Fin N → Fin N → ℝ) :
    (∑ i : Fin N, ∑ k : Fin N,
       a i * a k * (∑ j : Fin N, w j * f i j * f k j)) =
    ∑ j : Fin N, w j * (∑ i : Fin N, a i * f i j) ^ 2 := by
  calc
    _ = ∑ i : Fin N, ∑ k : Fin N, ∑ j : Fin N,
          a i * a k * (w j * f i j * f k j) := by
            simp only [Finset.mul_sum]
    _ = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
          a i * a k * (w j * f i j * f k j) := by
            apply Finset.sum_congr rfl
            intro i _
            exact Finset.sum_comm
    _ = ∑ j : Fin N, ∑ i : Fin N, ∑ k : Fin N,
          a i * a k * (w j * f i j * f k j) := Finset.sum_comm
    _ = ∑ j : Fin N, w j * (∑ i : Fin N, a i * f i j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            simp only [sq, Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro k _
            ring

theorem innovationCov_full_psd (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (N : ℕ) (a : Fin N → ℝ) :
    0 ≤ ∑ k : Fin N, ∑ l : Fin N,
         a k * a l * innovationCov x N k l := by
  rw [show (∑ k : Fin N, ∑ l : Fin N,
      a k * a l * innovationCov x N k l) =
      ∑ j : Fin N, weight x j.val *
        (∑ k : Fin N, a k * feature x k.val j.val) ^ 2 from
        gram_algebra N a (fun j => weight x j.val)
          (fun k j => feature x k.val j.val)]
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg
  · exact mul_nonneg (sub_nonneg.mpr hx1) (pow_nonneg hx0 _)
  · exact sq_nonneg _

/-- The first covariance column is exactly (1-x) times the mean vector. -/
theorem source_first_column (x : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    GppPrimeThresholdSourceCovariance.thresholdCov x k 1 = (1 - x) * x ^ k := by
  rw [GppPrimeThresholdSourceCovariance.covariance_symm,
      GppPrimeThresholdSourceCovariance.covariance_of_le x 1 k hk]
  simp only [pow_one]
  ring

end GppPrimeThresholdFullGram

#print axioms GppPrimeThresholdFullGram.innovationCov_full_psd
#print axioms GppPrimeThresholdFullGram.source_first_column

namespace GppPrimeThresholdFullGram

private theorem innovationCov_symm (x : ℝ) (N : ℕ) (k l : Fin N) :
    innovationCov x N k l = innovationCov x N l k := by
  unfold innovationCov
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem reversed_geometric (x : ℝ) (k l : ℕ) :
    (1 - x) * (∑ j ∈ Finset.range (k + 1),
       x ^ ((k + 1) + (l + 1) - (j + 1))) =
    x ^ (l + 1) * (1 - x ^ (k + 1)) := by
  have hrev :
      (∑ j ∈ Finset.range (k + 1),
          x ^ ((k + 1) + (l + 1) - (j + 1))) =
      (∑ j ∈ Finset.range (k + 1), x ^ ((l + 1) + j)) := by
    calc
      _ = ∑ j ∈ Finset.range (k + 1),
            x ^ ((k + 1) + (l + 1) - (((k + 1) - 1 - j) + 1)) := by
              rw [← Finset.sum_range_reflect]
      _ = _ := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjlt : j < k + 1 := Finset.mem_range.mp hj
              congr 1
              omega
  rw [hrev]
  have hgeo := GppPrimeThresholdSourceCovariance.finite_geometric_tail x (l + 1) (k + 1)
  rw [hgeo, pow_add]
  ring

private theorem innovationCov_of_le (x : ℝ) (N : ℕ) (k l : Fin N)
    (hkl : k.val ≤ l.val) :
    innovationCov x N k l =
      (1 - x) * (∑ j ∈ Finset.range (k.val + 1),
       x ^ ((k.val + 1) + (l.val + 1) - (j + 1))) := by
  unfold innovationCov
  change (∑ j : Fin N, (fun t : ℕ =>
    weight x t * feature x k.val t * feature x l.val t) j.val) = _
  rw [Fin.sum_univ_eq_sum_range]
  have hs : Finset.range (k.val + 1) ⊆ Finset.range N := by
    exact Finset.range_mono (Nat.succ_le_of_lt k.isLt)
  have hcrop :
      (∑ j ∈ Finset.range N,
         weight x j * feature x k.val j * feature x l.val j) =
      (∑ j ∈ Finset.range (k.val + 1),
         weight x j * feature x k.val j * feature x l.val j) := by
    symm
    apply Finset.sum_subset hs
    intro j hjN hjnot
    have hjgt : k.val < j := by
      have hn : ¬ j < k.val + 1 := by simpa using hjnot
      omega
    simp [feature, not_le.mpr hjgt]
  rw [hcrop, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ k.val := by
    have hjlt : j < k.val + 1 := Finset.mem_range.mp hj
    omega
  have hjl : j ≤ l.val := le_trans hjle hkl
  simp only [weight, feature, if_pos hjle, if_pos hjl]
  have hexp : (j + 1) + (k.val - j) + (l.val - j) =
      (k.val + 1) + (l.val + 1) - (j + 1) := by omega
  calc
    (1 - x) * x ^ (j + 1) * x ^ (k.val - j) * x ^ (l.val - j) =
       (1 - x) * x ^ ((j + 1) + (k.val - j) + (l.val - j)) := by
          rw [pow_add, pow_add]
          ring
    _ = _ := by rw [hexp]

/-- The finite innovation Gram is exactly the physical centered threshold covariance. -/
theorem innovationCov_eq_thresholdCov (x : ℝ) (N : ℕ) (k l : Fin N) :
    innovationCov x N k l =
      GppPrimeThresholdSourceCovariance.thresholdCov x (k.val + 1) (l.val + 1) := by
  rcases le_total k.val l.val with hkl | hlk
  · rw [innovationCov_of_le x N k l hkl, reversed_geometric]
    rw [GppPrimeThresholdSourceCovariance.covariance_of_le x (k.val + 1)
      (l.val + 1) (Nat.succ_le_succ hkl)]
  · rw [innovationCov_symm x N k l, innovationCov_of_le x N l k hlk,
        reversed_geometric,
        GppPrimeThresholdSourceCovariance.covariance_symm x (k.val + 1) (l.val + 1)]
    rw [GppPrimeThresholdSourceCovariance.covariance_of_le x (l.val + 1)
      (k.val + 1) (Nat.succ_le_succ hlk)]

/-- All-dimensional PSD for the actual centered geometric threshold covariance. -/
theorem thresholdCov_full_psd (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (N : ℕ) (a : Fin N → ℝ) :
    0 ≤ ∑ k : Fin N, ∑ l : Fin N,
       a k * a l * GppPrimeThresholdSourceCovariance.thresholdCov x
         (k.val + 1) (l.val + 1) := by
  simpa only [← innovationCov_eq_thresholdCov x N] using
    innovationCov_full_psd x hx0 hx1 N a

end GppPrimeThresholdFullGram

#print axioms GppPrimeThresholdFullGram.thresholdCov_full_psd
