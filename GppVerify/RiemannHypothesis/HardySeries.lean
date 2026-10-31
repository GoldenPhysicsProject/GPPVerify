import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# The Hardy potential series `log coth(z/2) = 2 Σ_{n odd} e^{-nz}/n`

Source: Codex/Discovery2, GPP-bridge PR #11 comments 2026-10-31 ("quartic Hardy curvature":
`H(z) = log coth(z/2) = 2 Σ_{n odd ≥ 1} e^{-nz}/n`, so that `V_L(a+u) = H(a+u)/2 + H(a−u)/2`
has an explicit cosh series). Daniel Toupin / Golden Physics Project, with AI assistance from Codex
(statement) and Claude Code (formalization).

* `hardy_series`: for `z > 0`, `HasSum (k ↦ 2/(2k+1) · e^{-(2k+1)z}) (log (cosh(z/2)/sinh(z/2)))`
  (the Mercator-type series for `log((1+x)/(1−x))` at `x = e^{-z}`).
* `hardy_sum_two`: for `|u| < a` (so `a > 0`), the sum `H(a+u) + H(a−u)` has the series
  `Σ_k 4/(2k+1) · e^{-(2k+1)a} · cosh((2k+1)u)`.

**Scope.** The series and the two-point cosh series only. The derivatives `H'' = cosh/sinh²`,
`H'''' = (cosh²+5)cosh/sinh⁴`, the quartic lower bound `V ≥ H(a) + H''(a)u²/2 + H''''(a)u⁴/24`,
and all use of these in the Weil form are not formalized. No claim about RH.
-/

set_option autoImplicit false

namespace GppHardySeries

/-- `log coth(z/2) = Σ_k 2/(2k+1) e^{-(2k+1) z}` for `z > 0`. -/
theorem hardy_series {z : ℝ} (hz : 0 < z) :
    HasSum (fun k : ℕ => 2 / (2 * (k : ℝ) + 1) * Real.exp (-((2 * (k : ℝ) + 1) * z)))
      (Real.log (Real.cosh (z / 2) / Real.sinh (z / 2))) := by
  set x : ℝ := Real.exp (-z) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by rw [hx, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have habs : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hterm : ∀ k : ℕ, 2 * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1) =
      2 / (2 * (k : ℝ) + 1) * Real.exp (-((2 * (k : ℝ) + 1) * z)) := by
    intro k
    have : x ^ (2 * k + 1) = Real.exp (-((2 * (k : ℝ) + 1) * z)) := by
      rw [hx, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]; ring
  have hlog : Real.log (1 + x) - Real.log (1 - x) = Real.log (Real.cosh (z / 2) / Real.sinh (z / 2)) := by
    have h1 : 0 < 1 + x := by linarith
    have h2 : 0 < 1 - x := by linarith
    rw [← Real.log_div h1.ne' h2.ne']
    congr 1
    have hu : 0 < Real.exp (z / 2) := Real.exp_pos _
    have hxe : x = (Real.exp (z / 2))⁻¹ * (Real.exp (z / 2))⁻¹ := by
      rw [hx, ← mul_inv, ← Real.exp_add]; rw [← Real.exp_neg]; congr 1; ring
    have hsinh : 0 < Real.sinh (z / 2) := Real.sinh_pos_iff.mpr (by linarith)
    rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg, hxe]
    have hne : Real.exp (z / 2) ^ 2 - 1 ≠ 0 := by
      intro h
      have : Real.exp (z / 2) ^ 2 = 1 := by linarith
      have h3 : 1 < Real.exp (z / 2) := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      nlinarith
    field_simp
  rw [← hlog]
  simpa only [hterm] using hs

/-- The two-point series: `H(a+u) + H(a−u) = Σ_k 4/(2k+1) e^{-(2k+1)a} cosh((2k+1)u)`. -/
theorem hardy_sum_two {a u : ℝ} (hu : |u| < a) :
    HasSum (fun k : ℕ => 4 / (2 * (k : ℝ) + 1) * Real.exp (-((2 * (k : ℝ) + 1) * a)) *
        Real.cosh ((2 * (k : ℝ) + 1) * u))
      (Real.log (Real.cosh ((a + u) / 2) / Real.sinh ((a + u) / 2)) +
        Real.log (Real.cosh ((a - u) / 2) / Real.sinh ((a - u) / 2))) := by
  have h1 : 0 < a + u := by linarith [neg_abs_le u]
  have h2 : 0 < a - u := by linarith [le_abs_self u]
  have hs := (hardy_series h1).add (hardy_series h2)
  convert hs using 1
  funext k
  have e1 : Real.exp (-((2 * (k : ℝ) + 1) * (a + u))) =
      Real.exp (-((2 * (k : ℝ) + 1) * a)) * Real.exp (-((2 * (k : ℝ) + 1) * u)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-((2 * (k : ℝ) + 1) * (a - u))) =
      Real.exp (-((2 * (k : ℝ) + 1) * a)) * Real.exp ((2 * (k : ℝ) + 1) * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have hc : Real.cosh ((2 * (k : ℝ) + 1) * u) =
      (Real.exp ((2 * (k : ℝ) + 1) * u) + Real.exp (-((2 * (k : ℝ) + 1) * u))) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg]
  rw [e1, e2, hc]
  ring

end GppHardySeries
