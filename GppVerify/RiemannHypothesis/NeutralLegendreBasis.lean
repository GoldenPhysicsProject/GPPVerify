import Mathlib.Tactic

/-!
# Pole-neutral shifted-Legendre exponentials: the exact `n = 2, 3` cases

Source: Astra, `work/2026-10-10_astra_pick_neutral_basis.md` (GPP-bridge), §2.

With `L_n(t) = P_n(2t-1)` the shifted Legendre polynomial and
`g_n(u) = 1_{u ≥ 0} e^{-3u/2} L_n(e^{-u})`, the Mellin-type transform is
`G_n(z) = ∫₀¹ t^{1/2-z} L_n(t) dt`, and the two pole moments are `G_n(±1/2)`, i.e. `∫ L_n` and `∫ t L_n`.

This file proves, as exact rational identities, for the explicit coefficient vectors
`L_2 = 1 - 6t + 6t²` and `L_3 = -1 + 12t - 30t² + 20t³` (these are `±` the shifted Legendre
polynomials `P_n(2t-1)`; the overall sign is irrelevant to the identities):

* both pole moments vanish (`moments_two`, `moments_three`);
* the termwise integral `G_n(z) = ∑_j c_j/(3/2 - z + j)` equals the product form
  `∏_{j<n}(1/2 - z - j) / ∏_{j≤n}(3/2 - z + j)` (`G_two`, `G_three`).

The general-`n` product formula (shifted Rodrigues + beta integral, Astra §2) was checked
here in exact `Fraction` arithmetic for `n = 2,…,8` and is **not** formalised for general `n`.

## Scope

Algebraic identities only. Nothing here says positivity of this basis suffices for RH;
the unrestricted Pick criterion is the target and is open. No RH claim.
-/

namespace GppNeutralLegendre

/-- Both pole moments of `L_2 = 1 - 6t + 6t²` vanish: `∫₀¹ L₂ = ∫₀¹ t L₂ = 0`
    (termwise `∑ c_j/(j+1)` and `∑ c_j/(j+2)`). -/
theorem moments_two :
    (1 / 1 - 6 / 2 + 6 / 3 : ℚ) = 0 ∧ (1 / 2 - 6 / 3 + 6 / 4 : ℚ) = 0 := by
  constructor <;> norm_num

/-- Both pole moments of `L_3 = -1 + 12t - 30t² + 20t³` vanish. -/
theorem moments_three :
    (-1 / 1 + 12 / 2 - 30 / 3 + 20 / 4 : ℚ) = 0 ∧
    (-1 / 2 + 12 / 3 - 30 / 4 + 20 / 5 : ℚ) = 0 := by
  constructor <;> norm_num

/-- `G_2` in the variable `a = 3/2 - z`: `1/a - 6/(a+1) + 6/(a+2) = (a-1)(a-2)/(a(a+1)(a+2))`.
    Since `a - 1 = 1/2 - z` and `a - 2 = -1/2 - z`, the right side is
    `(1/2 - z)(-1/2 - z)/((3/2 - z)(5/2 - z)(7/2 - z))`, i.e. `(z² - 1/4)/(…)`. -/
theorem G_two {a : ℝ} (h0 : a ≠ 0) (h1 : a + 1 ≠ 0) (h2 : a + 2 ≠ 0) :
    1 / a - 6 / (a + 1) + 6 / (a + 2) = (a - 1) * (a - 2) / (a * (a + 1) * (a + 2)) := by
  field_simp
  ring

/-- `G_3` in `a = 3/2 - z`: the product form `∏_{j<3}(1/2 - z - j) / ∏_{j≤3}(3/2 - z + j)`. -/
theorem G_three {a : ℝ} (h0 : a ≠ 0) (h1 : a + 1 ≠ 0) (h2 : a + 2 ≠ 0) (h3 : a + 3 ≠ 0) :
    -1 / a + 12 / (a + 1) - 30 / (a + 2) + 20 / (a + 3)
      = (a - 1) * (a - 2) * (a - 3) / (a * (a + 1) * (a + 2) * (a + 3)) := by
  field_simp
  ring

/-- The same, with `a = 3/2 - z` substituted: `G_2(z) = (z² - 1/4)/((3/2-z)(5/2-z)(7/2-z))`. -/
theorem G_two_z {z : ℝ} (h0 : 3 / 2 - z ≠ 0) (h1 : 3 / 2 - z + 1 ≠ 0) (h2 : 3 / 2 - z + 2 ≠ 0) :
    1 / (3 / 2 - z) - 6 / (3 / 2 - z + 1) + 6 / (3 / 2 - z + 2)
      = (z ^ 2 - 1 / 4) / ((3 / 2 - z) * (3 / 2 - z + 1) * (3 / 2 - z + 2)) := by
  rw [G_two h0 h1 h2]
  congr 1
  ring

end GppNeutralLegendre
