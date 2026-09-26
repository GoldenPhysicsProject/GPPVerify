import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-!
# Real logarithm series kernel for the regulated scalar box

The pinned Mathlib version proves

  sum_{n>=0} z^n/n = -Log(1-z)

on the open unit disk as `Complex.hasSum_taylorSeries_neg_log`. Its `n=0` term is
zero, so shifting the index and then using the real-axis `ofReal` embedding gives the
exact real form needed to identify the termwise derivative of the project's local
dilogarithm series.
-/

namespace GppRegulatedBoxLogSeriesKernel

/-- Real-axis shifted Taylor series for the negative logarithm. -/
theorem hasSum_pow_succ_div_succ_eq_neg_log
    {x : ℝ} (hx : |x| < 1) :
    HasSum
      (fun n : ℕ => x ^ (n + 1) / ((n + 1 : ℕ) : ℝ))
      (-Real.log (1 - x)) := by
  have hxc : ‖(x : ℂ)‖ < 1 := by
    simpa [Complex.norm_real] using hx
  have hcomplex :
      HasSum (fun n : ℕ => (x : ℂ) ^ n / (n : ℂ))
        (-Complex.log (1 - (x : ℂ))) :=
    Complex.hasSum_taylorSeries_neg_log hxc
  have htail :
      HasSum
        (fun n : ℕ => (x : ℂ) ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
        (-Complex.log (1 - (x : ℂ))) := by
    apply (hasSum_nat_add_iff
      (f := fun m : ℕ => (x : ℂ) ^ m / (m : ℂ)) 1).2
    simpa using hcomplex
  have hx1 : x < 1 := lt_of_le_of_lt (le_abs_self x) hx
  have hpos : 0 ≤ 1 - x := (sub_pos.mpr hx1).le
  rw [← Complex.hasSum_ofReal]
  convert htail using 1
  · funext n
    norm_cast
  · calc
      (((-Real.log (1 - x) : ℝ) : ℂ)) = -(Real.log (1 - x) : ℂ) := by norm_cast
      _ = -Complex.log ((1 - x : ℝ) : ℂ) := by rw [Complex.ofReal_log hpos]
      _ = -Complex.log (1 - (x : ℂ)) := by norm_cast

/-- After dividing by a nonzero `x`, the derivative series is exactly
`-log(1-x)/x`. -/
theorem hasSum_pow_div_succ_eq_neg_log_div
    {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasSum
      (fun n : ℕ => x ^ n / ((n + 1 : ℕ) : ℝ))
      (-Real.log (1 - x) / x) := by
  have h := (hasSum_pow_succ_div_succ_eq_neg_log hx).div_const x
  have hfun :
      (fun n : ℕ => x ^ n / ((n + 1 : ℕ) : ℝ)) =
        (fun n : ℕ => x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) / x) := by
    funext n
    have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    rw [pow_succ]
    field_simp [hx0, hn]
    ring
  rw [hfun]
  exact h

/-- `tsum` form used by the derivative theorem for `li2Series`. -/
theorem tsum_pow_div_succ_eq_neg_log_div
    {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    (∑' n : ℕ, x ^ n / ((n + 1 : ℕ) : ℝ)) =
      -Real.log (1 - x) / x :=
  (hasSum_pow_div_succ_eq_neg_log_div hx hx0).tsum_eq

end GppRegulatedBoxLogSeriesKernel

#print axioms GppRegulatedBoxLogSeriesKernel.hasSum_pow_succ_div_succ_eq_neg_log
#print axioms GppRegulatedBoxLogSeriesKernel.tsum_pow_div_succ_eq_neg_log_div
