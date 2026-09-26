import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-!
# Local dilogarithm power series for the regulated scalar box

The scalar-box regulator proof only needs a small-argument bound for the real
dilogarithm after its endpoint functional equations have been applied.  This file
builds that local object directly from its convergent power series, avoiding any
dependence on a pre-existing `Li₂` library API.

It does NOT prove the Spence or inversion identities.  Those remain a separate
analytic layer.
-/

namespace GppRegulatedBoxDilogSeries

/-- Real dilogarithm power series on its open disk of convergence. -/
noncomputable def li2Series (x : ℝ) : ℝ :=
  ∑' n : ℕ, x ^ (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2)

/-- Absolute convergence of the defining series for `|x| < 1`. -/
theorem summable_li2Series_terms {x : ℝ} (hx : |x| < 1) :
    Summable (fun n : ℕ => x ^ (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  have hgeom0 : Summable (fun n : ℕ => |x| ^ n) := by
    exact summable_geometric_of_abs_lt_one (by simpa using hx)
  have hgeom : Summable (fun n : ℕ => |x| ^ (n + 1)) := by
    simpa [pow_succ, mul_comm] using hgeom0.mul_left |x|
  apply Summable.of_norm_bounded (fun n : ℕ => |x| ^ (n + 1)) hgeom
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_pow]
  rw [abs_of_nonneg (sq_nonneg (((n + 1 : ℕ) : ℝ)))]
  have hden : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) ^ 2) := by
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith [sq_nonneg (((n + 1 : ℕ) : ℝ) - 1)]
  exact div_le_self (by positivity) hden

/-- The shifted geometric majorant has the exact sum `|x|/(1-|x|)`. -/
theorem tsum_abs_pow_succ {x : ℝ} (hx : |x| < 1) :
    (∑' n : ℕ, |x| ^ (n + 1)) = |x| / (1 - |x|) := by
  calc
    (∑' n : ℕ, |x| ^ (n + 1)) =
        ∑' n : ℕ, |x| * |x| ^ n := by
          apply tsum_congr
          intro n
          rw [pow_succ]
          ring
    _ = |x| * ∑' n : ℕ, |x| ^ n := by
          rw [tsum_mul_left]
    _ = |x| * (1 - |x|)⁻¹ := by
          rw [tsum_geometric_of_abs_lt_one (by simpa using hx)]
    _ = |x| / (1 - |x|) := by rw [div_eq_mul_inv]

/-- **Small-argument dilogarithm bound** obtained directly from the power series. -/
theorem abs_li2Series_le {x : ℝ} (hx : |x| < 1) :
    |li2Series x| ≤ |x| / (1 - |x|) := by
  let f : ℕ → ℝ := fun n => x ^ (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2)
  have hs : Summable f := by
    simpa [f] using summable_li2Series_terms hx
  have hgeom0 : Summable (fun n : ℕ => |x| ^ n) :=
    summable_geometric_of_abs_lt_one (by simpa using hx)
  have hgeom : Summable (fun n : ℕ => |x| ^ (n + 1)) := by
    simpa [pow_succ, mul_comm] using hgeom0.mul_left |x|
  have hterm : ∀ n : ℕ, ‖f n‖ ≤ |x| ^ (n + 1) := by
    intro n
    dsimp [f]
    rw [abs_div, abs_pow]
    rw [abs_of_nonneg (sq_nonneg (((n + 1 : ℕ) : ℝ)))]
    have hden : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) ^ 2) := by
      have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      nlinarith [sq_nonneg (((n + 1 : ℕ) : ℝ) - 1)]
    exact div_le_self (by positivity) hden
  have hnorm : ‖∑' n : ℕ, f n‖ ≤ ∑' n : ℕ, ‖f n‖ :=
    norm_tsum_le_tsum_norm hs.norm
  have hmono : (∑' n : ℕ, ‖f n‖) ≤ ∑' n : ℕ, |x| ^ (n + 1) :=
    tsum_mono hs.norm hgeom hterm
  unfold li2Series
  change |∑' n : ℕ, f n| ≤ |x| / (1 - |x|)
  rw [← Real.norm_eq_abs]
  exact hnorm.trans (hmono.trans_eq (tsum_abs_pow_succ hx))

/-- The exact form used for positive small arguments in the scalar-box remainder. -/
theorem abs_li2Series_le_of_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |li2Series x| ≤ x / (1 - x) := by
  have hxabs : |x| < 1 := by simpa [abs_of_nonneg hx0] using hx1
  simpa [abs_of_nonneg hx0] using abs_li2Series_le hxabs

/-- The same estimate for the negative small arguments occurring at the moving endpoint. -/
theorem abs_li2Series_neg_le_of_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |li2Series (-x)| ≤ x / (1 - x) := by
  have hxabs : |-x| < 1 := by simpa [abs_of_nonneg hx0] using hx1
  simpa [abs_of_nonneg hx0] using abs_li2Series_le hxabs

end GppRegulatedBoxDilogSeries

#print axioms GppRegulatedBoxDilogSeries.abs_li2Series_le
#print axioms GppRegulatedBoxDilogSeries.abs_li2Series_neg_le_of_nonneg
