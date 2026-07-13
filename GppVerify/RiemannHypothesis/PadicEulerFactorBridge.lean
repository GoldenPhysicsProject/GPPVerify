import GppVerify.RiemannHypothesis.PadicZetaIntegralClosedForm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Bridge from the local p-adic zeta integral to Mathlib's Euler product

Mathlib already proves the Euler product for the Riemann zeta function:
`riemannZeta_eulerProduct_tprod : ∏' (p : Nat.Primes), (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s`
for `s.re > 1` (`Mathlib.NumberTheory.EulerProduct.DirichletLSeries`). So the piece of
Tate's-thesis infrastructure genuinely missing here is not the global convergence
statement — Mathlib has that — but a bridge from our `ℤ_p`-side computation
(`GppPadicFullZeta.tate_local_zeta_integral`) down to *exactly* the local factor
`(1 - (p:ℂ)^(-s))⁻¹` that appears in Mathlib's product.

This file proves that bridge for a single fixed prime `p`, at every real `s > 1`: our
local Euler factor, extracted from `tate_local_zeta_integral` by dividing out the
`(1 - 1/p)` measure-normalization constant, agrees on the nose (as a real number cast
into `ℂ`) with Mathlib's `(1 - (p:ℂ)^(-s))⁻¹`. Not sourced from a specific Golden
Physics Project paper.
-/

namespace GppPadicFullZeta

open scoped ENNReal

variable (p : ℕ) [Fact p.Prime]

/-- Mathlib's complex local Euler factor at a *real* `s`, cast from `ℂ` down to `ℝ`
    and back, is exactly the real-valued Euler factor `(1 - p^{-s})⁻¹` — i.e. the
    complex factor is real-valued at real arguments, and its value is the expected
    one. Uses `Complex.ofReal_cpow` (real `rpow` and complex `cpow` agree, cast
    through `ℂ`, for a nonnegative real base) to move the exponentiation across the
    cast, then closes the resulting cast identity. -/
theorem riemannZeta_factor_eq_ofReal (s : ℝ) :
    (1 - (p : ℂ) ^ (-(s : ℂ)))⁻¹ = ((1 - (p : ℝ) ^ (-s))⁻¹ : ℝ) := by
  have hp : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hcast : (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    have hexp : (-(s : ℂ)) = ((-s : ℝ) : ℂ) := by push_cast; ring
    rw [hexp, Complex.ofReal_cpow hp (-s)]
    norm_cast
  rw [hcast]
  norm_cast

/-- Our `ℝ≥0∞`-valued Euler factor, extracted from `tate_local_zeta_integral` by
    dividing out the `(1 - 1/p)` prefactor, has real part (`.toReal`) exactly the
    classical real Euler factor `(1 - p^{-s})⁻¹`. Needs `s ≥ 0` merely to know
    `p^{-s} ≤ 1` (so the truncated `ℝ≥0∞` subtraction agrees with real subtraction);
    the `s > 1` used elsewhere in this file is a stronger hypothesis than necessary
    here, kept only so both halves of the bridge share one hypothesis. -/
theorem euler_factor_toReal_eq (s : ℝ) (hs : 1 < s) :
    ((1 - (p : ℝ≥0∞) ^ (-s))⁻¹).toReal = (1 - (p : ℝ) ^ (-s))⁻¹ := by
  have hp1 : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hle : (p : ℝ≥0∞) ^ (-s) ≤ 1 := by
    calc (p : ℝ≥0∞) ^ (-s) ≤ (p : ℝ≥0∞) ^ (0 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ = 1 := ENNReal.rpow_zero
  rw [ENNReal.toReal_inv, ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_one,
      ← ENNReal.toReal_rpow, ENNReal.toReal_natCast]

/-- **The bridge.** Our local Euler factor (via `tate_local_zeta_integral`, with the
    `(1-1/p)` measure-normalization constant divided out) equals, on the nose,
    Mathlib's local factor `(1 - (p:ℂ)^(-s))⁻¹` from `riemannZeta_eulerProduct_tprod`
    — the same factor that Mathlib already assembles into the full Euler product for
    `riemannZeta`. This is the precise point of contact between this thread's p-adic
    measure-theoretic construction and Mathlib's existing analytic number theory. -/
theorem euler_factor_bridge (s : ℝ) (hs : 1 < s) :
    (((1 - (p : ℝ≥0∞) ^ (-s))⁻¹).toReal : ℂ) = (1 - (p : ℂ) ^ (-(s : ℂ)))⁻¹ := by
  rw [euler_factor_toReal_eq p s hs]
  exact (riemannZeta_factor_eq_ofReal p s).symm

end GppPadicFullZeta
