import GppVerify.CelestialHolography.RegulatedBoxDilogSeries
import GppVerify.CelestialHolography.RegulatedBoxLogSeriesKernel
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
# Derivative of the local regulated-box dilogarithm series

For `0 < x < 1`, differentiate the defining real power series term-by-term on a
smaller open interval contained in `(-1,1)`. The derivative terms are dominated by
a geometric series `q^n`, where `x < q < 1`. The derivative series is then identified
with `-log(1-x)/x` using `RegulatedBoxLogSeriesKernel`.
-/

namespace GppRegulatedBoxDilogDerivative

open Set
open GppRegulatedBoxDilogSeries
open GppRegulatedBoxLogSeriesKernel

/-- Derivative of one dilogarithm power-series term. -/
theorem hasDerivAt_li2_term (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => y ^ (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2))
      (x ^ n / ((n + 1 : ℕ) : ℝ)) x := by
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  convert (hasDerivAt_pow (n + 1) x).div_const ((((n + 1 : ℕ) : ℝ) ^ 2)) using 1 <;>
    field_simp [hn] <;> ring

/-- The defining local dilogarithm series has the classical real derivative on `0<x<1`. -/
theorem hasDerivAt_li2Series
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt li2Series (-Real.log (1 - x) / x) x := by
  let q : ℝ := (x + 1) / 2
  have hxq : x < q := by
    dsimp [q]
    linarith
  have hq1 : q < 1 := by
    dsimp [q]
    linarith
  have hq0 : 0 < q := hx0.trans hxq
  have hqabs : |q| < 1 := by simpa [abs_of_pos hq0] using hq1
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
    exact ⟨by linarith, hxq⟩
  have H := hasDerivAt_tsum_of_isPreconnected
    hgeom isOpen_Ioo isPreconnected_Ioo hderiv hbound hzero_mem hzero hxmem
  have hsum :
      (∑' n : ℕ, g' n x) = -Real.log (1 - x) / x := by
    have hxabs : |x| < 1 := by simpa [abs_of_pos hx0] using hx1
    simpa [g'] using tsum_pow_div_succ_eq_neg_log_div hxabs hx0.ne'
  rw [hsum] at H
  change HasDerivAt (fun z : ℝ => ∑' n : ℕ, g n z) (-Real.log (1 - x) / x) x
  exact H

end GppRegulatedBoxDilogDerivative

#print axioms GppRegulatedBoxDilogDerivative.hasDerivAt_li2_term
#print axioms GppRegulatedBoxDilogDerivative.hasDerivAt_li2Series
