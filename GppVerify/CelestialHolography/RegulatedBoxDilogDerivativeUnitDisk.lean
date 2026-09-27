import GppVerify.CelestialHolography.RegulatedBoxDilogDerivative
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
# Real dilogarithm derivative on the punctured open unit disk

The local regulated-box dilogarithm series is defined for every real input.  The
termwise-differentiation argument used on `(0,1)` only needs a geometric majorant,
and therefore extends verbatim to every nonzero real `x` with `|x| < 1` by choosing

  q = (|x| + 1) / 2.

This extension is the missing concrete bridge to negative arguments.  In particular,
it supplies the derivative hypothesis needed by the branch-free Landen and reciprocal
inversion kernels while remaining entirely inside the real power-series domain.
-/

namespace GppRegulatedBoxDilogDerivativeUnitDisk

open Set
open GppRegulatedBoxDilogSeries
open GppRegulatedBoxLogSeriesKernel
open GppRegulatedBoxDilogDerivative

/-- The project's real dilogarithm series has the classical derivative at every
nonzero point of the open unit disk. -/
theorem hasDerivAt_li2Series_of_abs_lt_one
    {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasDerivAt li2Series (-Real.log (1 - x) / x) x := by
  let q : ℝ := (|x| + 1) / 2
  have hxq : |x| < q := by
    dsimp [q]
    linarith
  have hq1 : q < 1 := by
    dsimp [q]
    linarith
  have hq0 : 0 < q := by
    have hxn : 0 ≤ |x| := abs_nonneg x
    dsimp [q]
    linarith
  have hqabs : |q| < 1 := by
    simpa [abs_of_pos hq0] using hq1
  have hgeom : Summable (fun n : ℕ => q ^ n) := by
    exact summable_geometric_of_abs_lt_one hqabs
  let g : ℕ → ℝ → ℝ := fun n y =>
    y ^ (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2)
  let g' : ℕ → ℝ → ℝ := fun n y =>
    y ^ n / ((n + 1 : ℕ) : ℝ)
  have hderiv : ∀ n y, y ∈ Ioo (-q) q → HasDerivAt (g n) (g' n y) y := by
    intro n y hy
    simpa [g, g'] using hasDerivAt_li2_term n y
  have hbound : ∀ n y, y ∈ Ioo (-q) q → ‖g' n y‖ ≤ q ^ n := by
    intro n y hy
    have hyabs : |y| < q := by
      rw [abs_lt]
      exact ⟨hy.1, hy.2⟩
    have hyq : |y| ≤ q := hyabs.le
    have hpow : |y| ^ n ≤ q ^ n := by
      exact pow_le_pow_left₀ (abs_nonneg y) hyq n
    have hden : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    dsimp [g']
    rw [abs_div, abs_pow, abs_of_nonneg (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]
    calc
      |y| ^ n / ((n + 1 : ℕ) : ℝ) ≤ |y| ^ n :=
        div_le_self (pow_nonneg (abs_nonneg y) n) hden
      _ ≤ q ^ n := hpow
  have hzero : Summable (fun n : ℕ => g n 0) := by
    simpa [g] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  have hzero_mem : (0 : ℝ) ∈ Ioo (-q) q := by
    exact ⟨by linarith, hq0⟩
  have hxmem : x ∈ Ioo (-q) q := by
    exact abs_lt.mp hxq
  have H := hasDerivAt_tsum_of_isPreconnected
    hgeom isOpen_Ioo isPreconnected_Ioo hderiv hbound hzero_mem hzero hxmem
  have hsum :
      (∑' n : ℕ, g' n x) = -Real.log (1 - x) / x := by
    simpa [g'] using tsum_pow_div_succ_eq_neg_log_div hx hx0
  rw [hsum] at H
  change HasDerivAt (fun z : ℝ => ∑' n : ℕ, g n z) (-Real.log (1 - x) / x) x
  exact H

/-- Negative-axis specialization used by the real inversion/Landen identities. -/
theorem hasDerivAt_li2Series_neg
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt li2Series (-Real.log (1 + x) / (-x)) (-x) := by
  have habs : |(-x : ℝ)| < 1 := by
    simpa [abs_of_pos hx0] using hx1
  have hne : (-x : ℝ) ≠ 0 := neg_ne_zero.mpr hx0.ne'
  simpa using hasDerivAt_li2Series_of_abs_lt_one habs hne

end GppRegulatedBoxDilogDerivativeUnitDisk

#print axioms GppRegulatedBoxDilogDerivativeUnitDisk.hasDerivAt_li2Series_of_abs_lt_one
#print axioms GppRegulatedBoxDilogDerivativeUnitDisk.hasDerivAt_li2Series_neg
