import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The two-logistic density as a Ward operator applied to the Bose trace

Source: Codex, GPPDiscovery2 `research/2026-09-27_logistic_tfd_mellin_zeta_ward.md`, §2.

Let `h(y) = 1/(e^y − 1) = Σ_{n≥1} e^{-ny}` be the Bose trace. The note shows the density of the sum
of two independent standard logistic variables is, for `y ≠ 0`,
`g(y) = (y coth(y/2) − 2)/(4 sinh²(y/2))`, and that
`g(y) = y h''(y) + 2 h'(y)`, equivalently `y g(y) = D(D+1) h(y)` with `D = y d/dy`.

* `hasDerivAt_bose`, `hasDerivAt_bose'`: `h' = −e^y/(e^y−1)²` and
  `h'' = e^y(e^y+1)/(e^y−1)³` for `y ≠ 0`;
* `logistic_conv_eq_ward`: the closed form of `g` equals `y h'' + 2 h'` for `y ≠ 0`.

## Checks and scope

The identity checks (both sides reduce to `e^y [y(e^y+1) − 2(e^y−1)]/(e^y−1)³`). **Not formalized:**
that the convolution of two logistic densities *is* this `g` (a convolution integral), the
characteristic function `πλ/sinh πλ` of the logistic density, and the Mellin identity
`∫ y^s g = s(s−1)Γ(s)ζ(s)` (§§3–4), which needs integration by parts against `Γ(s)ζ(s)`. No RH claim.
-/

open Real

namespace GppLogisticBose

/-- The Bose trace `h(y) = 1/(e^y − 1)`. -/
noncomputable def bose (y : ℝ) : ℝ := 1 / (Real.exp y - 1)

/-- `h'`. -/
noncomputable def bose1 (y : ℝ) : ℝ := -Real.exp y / (Real.exp y - 1) ^ 2

/-- `h''`. -/
noncomputable def bose2 (y : ℝ) : ℝ := Real.exp y * (Real.exp y + 1) / (Real.exp y - 1) ^ 3

/-- The closed form `(y coth(y/2) − 2)/(4 sinh²(y/2))` of the two-logistic density. -/
noncomputable def twoLogistic (y : ℝ) : ℝ :=
  (y * (Real.cosh (y / 2) / Real.sinh (y / 2)) - 2) / (4 * Real.sinh (y / 2) ^ 2)

theorem exp_sub_one_ne (y : ℝ) (hy : y ≠ 0) : Real.exp y - 1 ≠ 0 := by
  intro h
  have : Real.exp y = 1 := by linarith
  exact hy (Real.exp_eq_one_iff y |>.mp this)

theorem hasDerivAt_bose (y : ℝ) (hy : y ≠ 0) : HasDerivAt bose (bose1 y) y := by
  have h := exp_sub_one_ne y hy
  have h1 : HasDerivAt (fun y => Real.exp y - 1) (Real.exp y) y :=
    (Real.hasDerivAt_exp y).sub_const 1
  have h2 := h1.inv h
  have e : bose = fun y => (Real.exp y - 1)⁻¹ := by
    funext z; simp [bose, one_div]
  rw [e]
  exact h2

theorem hasDerivAt_bose' (y : ℝ) (hy : y ≠ 0) : HasDerivAt bose1 (bose2 y) y := by
  have h := exp_sub_one_ne y hy
  have h1 : HasDerivAt (fun y => Real.exp y - 1) (Real.exp y) y :=
    (Real.hasDerivAt_exp y).sub_const 1
  have h2 : HasDerivAt (fun y => (Real.exp y - 1) ^ 2) (2 * (Real.exp y - 1) * Real.exp y) y := by
    have := h1.fun_pow 2
    simpa using this
  have h3 := ((Real.hasDerivAt_exp y).neg).div h2 (pow_ne_zero 2 h)
  have e : bose1 = fun y => -Real.exp y / (Real.exp y - 1) ^ 2 := by
    funext z; rfl
  rw [e]
  refine h3.congr_deriv ?_
  unfold bose2
  simp only [Pi.neg_apply]
  field_simp
  ring

/-- **The two-logistic density is `y h'' + 2 h'`.** -/
theorem logistic_conv_eq_ward (y : ℝ) (hy : y ≠ 0) :
    twoLogistic y = y * bose2 y + 2 * bose1 y := by
  have h := exp_sub_one_ne y hy
  have e1 : Real.exp y = Real.exp (y / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE : Real.exp (y / 2) ≠ 0 := (Real.exp_pos _).ne'
  have hsin : Real.sinh (y / 2) = (Real.exp (y / 2) - (Real.exp (y / 2))⁻¹) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg]
  have hcos : Real.cosh (y / 2) = (Real.exp (y / 2) + (Real.exp (y / 2))⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg]
  unfold twoLogistic bose1 bose2
  rw [e1] at h ⊢
  set E := Real.exp (y / 2) with hEdef
  rw [hsin, hcos] at *
  have hE1 : E ^ 2 - 1 ≠ 0 := h
  have hE2 : E - E⁻¹ ≠ 0 := by
    intro hz; apply hE1
    have : E ^ 2 - 1 = E * (E - E⁻¹) := by field_simp
    rw [this, hz, mul_zero]
  field_simp
  ring

end GppLogisticBose
