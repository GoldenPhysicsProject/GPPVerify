import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Li moments of a reflected zero quartet: `4[1 − cosh(nε) cos(nθ)]`

Source: Codex, GPP-bridge `work/codex/2026-10-13_arithmetic_seed_euler_horodisk_li_circle_moments.md`
(commit 88b7fe2; PR #11 comment 6160037777).

An off-line zero `ρ`, its conjugate, and their functional-equation reflections have Cayley images
`w = (ρ−1)/ρ` of the form `e^{−ε ± iθ}` and `e^{ε ± iθ}` (shadow = inversion, conjugation =
reflection). Their contribution to the `n`-th Li moment `Σ (1 − w^n)` is:
* `quartet_moment`: `Σ_{quartet} (1 − w^n) = 4 [1 − cosh(nε) cos(nθ)]`.
* `pair_moment`: for an on-circle conjugate pair (`ε = 0`), `2 [1 − cos(nθ)] ≥ 0`
  (`pair_moment_nonneg`).

So an off-line quartet gives a radial factor `cosh(nε) > 1`, which needs `n ≳ 1/ε ≈ γ²/δ` to resolve.
For DH's zero at `0.8085 + 85.70 i`, `1/ε ≈ 23806.5` (checked numerically in the PR). The Li
criterion is an equivalence, not a mechanism. **No RH claim.**
-/

namespace GppLiQuartetMoment

open Complex

theorem exp_pow (a : ℂ) (n : ℕ) : exp a ^ n = exp (n * a) := by
  rw [← Complex.exp_nat_mul]

/-- **Quartet Li moment**: `Σ (1 − w^n)` over `e^{−ε ± iθ}, e^{ε ± iθ}` is
`4[1 − cosh(nε) cos(nθ)]`. -/
theorem quartet_moment (ε θ : ℝ) (n : ℕ) :
    (1 - exp (-ε + θ * I) ^ n) + (1 - exp (-ε - θ * I) ^ n) + (1 - exp (ε + θ * I) ^ n) +
        (1 - exp (ε - θ * I) ^ n) =
      4 * (1 - (Real.cosh (n * ε) * Real.cos (n * θ) : ℝ)) := by
  simp only [exp_pow]
  push_cast
  rw [Complex.cosh, Complex.cos]
  have e1 : exp (↑n * (-↑ε + ↑θ * I)) = exp (-(↑n * ↑ε)) * exp (↑n * ↑θ * I) := by
    rw [← Complex.exp_add]; ring_nf
  have e2 : exp (↑n * (-↑ε - ↑θ * I)) = exp (-(↑n * ↑ε)) * exp (-(↑n * ↑θ * I)) := by
    rw [← Complex.exp_add]; ring_nf
  have e3 : exp (↑n * (↑ε + ↑θ * I)) = exp (↑n * ↑ε) * exp (↑n * ↑θ * I) := by
    rw [← Complex.exp_add]; ring_nf
  have e4 : exp (↑n * (↑ε - ↑θ * I)) = exp (↑n * ↑ε) * exp (-(↑n * ↑θ * I)) := by
    rw [← Complex.exp_add]; ring_nf
  rw [e1, e2, e3, e4]
  have hI : (-(↑n * ↑θ) * I) = -(↑n * ↑θ * I) := by ring
  rw [hI]
  ring

/-- **On-circle pair**: `(1 − e^{inθ}) + (1 − e^{−inθ}) = 2[1 − cos(nθ)]`. -/
theorem pair_moment (θ : ℝ) (n : ℕ) :
    (1 - exp (θ * I) ^ n) + (1 - exp (-(θ * I)) ^ n) = 2 * (1 - (Real.cos (n * θ) : ℝ)) := by
  simp only [exp_pow]
  push_cast
  rw [Complex.cos]
  have hI : (↑n * θ * I) = (↑n * (↑θ * I)) := by ring
  have hJ : (-(↑n * ↑θ) * I) = ↑n * -(↑θ * I) := by ring
  rw [← hI, hJ]
  ring

theorem pair_moment_nonneg (θ : ℝ) (n : ℕ) : 0 ≤ 2 * (1 - Real.cos (n * θ)) := by
  have := Real.cos_le_one (n * θ); linarith

end GppLiQuartetMoment
