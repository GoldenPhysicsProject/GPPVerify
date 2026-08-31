import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# The digamma function `ψ = Γ'/Γ`, from Mathlib's `Gamma` calculus

Blocked in earlier rounds on "Mathlib has no digamma/polygamma function" (a `grep` for the
*name* `digamma`/`polygamma` in `.lake/packages/mathlib/` genuinely returns zero hits at the
pinned `v4.19.0` commit). That grep was the wrong question: Mathlib's
`NumberTheory.Harmonic.GammaDeriv` already computes `deriv Real.Gamma` in closed form at `1`
and at `1/2` (`Real.hasDerivAt_Gamma_one`, `Real.hasDerivAt_Gamma_one_half`), via the
Bohr–Mollerup convexity argument and Legendre's duplication formula respectively — exactly
the two digamma special values `kinematic_block_v1.tex`'s First Moment Theorem needs
(`ψ(1) = -γ`, `ψ(1/2) = -γ - 2 log 2`). Defining `digamma := deriv Gamma / Gamma` on top of
this makes both immediate corollaries, along with the standard functional equation and the
values at all positive integers.

This file is the *real*-argument digamma function only. `kinematic_block_v1.tex`'s moment
integral needs `Re ψ(1/2 + iλ/2)`, the *complex* digamma along a vertical line — a further,
separate extension not attempted here (see `docs/FORMALIZATION_PLAN.md`).
-/

namespace GppDigamma

open Real Filter

local notation "γ" => Real.eulerMascheroniConstant

/-- The digamma function `ψ(x) = Γ'(x)/Γ(x)`, via Mathlib's `Real.Gamma` and its `deriv`.
    Junk-valued (via `Gamma`'s own junk value and division by zero) at the nonpositive
    integers, where `Gamma` itself is not differentiable. -/
noncomputable def digamma (x : ℝ) : ℝ := deriv Real.Gamma x / Real.Gamma x

/-- **`ψ(1) = -γ`**, the Euler–Mascheroni constant. -/
theorem digamma_one : digamma 1 = -γ := by
  unfold digamma
  rw [Real.hasDerivAt_Gamma_one.deriv, Real.Gamma_one]
  ring

/-- **`ψ(1/2) = -γ - 2 log 2`**, via Legendre's duplication formula (already differentiated
    in Mathlib as `Real.hasDerivAt_Gamma_one_half`). -/
theorem digamma_one_half : digamma (1 / 2) = -γ - 2 * Real.log 2 := by
  unfold digamma
  rw [Real.hasDerivAt_Gamma_one_half.deriv, Real.Gamma_one_half_eq]
  have hpi : Real.sqrt π ≠ 0 := by positivity
  field_simp
  ring

/-- **`ψ(n+1) = -γ + harmonic n`** for every natural `n`, from Mathlib's closed form for
    `deriv Gamma` at positive integers. -/
theorem digamma_nat_add_one (n : ℕ) :
    digamma ((n : ℝ) + 1) = -γ + (harmonic n : ℝ) := by
  unfold digamma
  rw [Real.hasDerivAt_Gamma_nat n |>.deriv, Real.Gamma_nat_eq_factorial]
  have hfact : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

/-- **Functional equation** `ψ(x+1) = ψ(x) + 1/x`, for `x` avoiding the poles of `Gamma`. -/
theorem digamma_add_one {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) :
    digamma (x + 1) = digamma x + 1 / x := by
  have hx0 : x ≠ 0 := by simpa using hx 0
  have hGx_diff : DifferentiableAt ℝ Real.Gamma x := Real.differentiableAt_Gamma hx
  have hGx_ne : Real.Gamma x ≠ 0 := Real.Gamma_ne_zero hx
  have hderivGx : HasDerivAt Real.Gamma (deriv Real.Gamma x) x := hGx_diff.hasDerivAt
  have hmul : HasDerivAt (fun s : ℝ => s * Real.Gamma s)
      (1 * Real.Gamma x + x * deriv Real.Gamma x) x := by
    have h := (hasDerivAt_id x).mul hderivGx
    simpa [Pi.div_def] using h
  -- `Gamma (s+1) = s * Gamma s` fails literally at `s = 0` (Mathlib's junk value gives
  -- `Gamma 1 = 1 ≠ 0 = 0 * Gamma 0`), so this can only be an equality of functions on a
  -- neighborhood of `x` avoiding `0`, not a global `funext` — matching the same care
  -- `NumberTheory.Harmonic.GammaDeriv`'s own `hder_rec` takes for the analogous step.
  have heq : (fun s : ℝ => s * Real.Gamma s) =ᶠ[nhds x] fun s : ℝ => Real.Gamma (s + 1) := by
    filter_upwards [eventually_ne_nhds hx0] with s hs using (Real.Gamma_add_one hs).symm
  have hderiv_eq : deriv (fun s : ℝ => s * Real.Gamma s) x
      = deriv (fun s : ℝ => Real.Gamma (s + 1)) x := heq.deriv_eq
  have hderiv_shift : deriv (fun s : ℝ => Real.Gamma (s + 1)) x = deriv Real.Gamma (x + 1) :=
    deriv_comp_add_const Real.Gamma 1 x
  have hval : deriv Real.Gamma (x + 1) = 1 * Real.Gamma x + x * deriv Real.Gamma x := by
    rw [← hderiv_shift, ← hderiv_eq]; exact hmul.deriv
  have hGamma_add_one : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one hx0
  unfold digamma
  rw [hval, hGamma_add_one]
  field_simp
  ring

end GppDigamma
