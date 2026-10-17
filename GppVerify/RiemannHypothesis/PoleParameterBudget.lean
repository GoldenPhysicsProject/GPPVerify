import Mathlib.Tactic

/-!
# Pole-parameter square completion and the necessary budget

Source: Codex's follow-up to Astra's even positive-pole lemma and Grok S26
(draft PR #367, `codex/even-positive-pole-direct-sum-20261015`). That draft overlaps the real
two-channel Cauchy lemmas already in `GppPositivePoleCompletion` (PR #365/#382), and its own
description asks that only the non-duplicate optimization lemmas be transferred; this file is exactly
those three lemmas, with the variable `λ` (a keyword in Lean 4) renamed `lam`. Authorship of the
mathematics: Codex/GPT.

* `pole_lambda_square_identity`: `(d+½)(a − 2bλ + (d+½)λ²) = (d+½)a − b² + ((d+½)λ − b)²`.
* `pole_lambda_lower_bound`: `(d+½)a − b² ≤ (d+½)(a − 2bλ + (d+½)λ²)` (the optimal `λ` quadratic).
* `necessary_pole_lambda_budget`: `C(β + λ²/2) < 1` forces `Cλ² < 2` for `C > 0`, `β ≥ 0`.

The last one is the geometry behind Grok's S26 `h = ½` bound (`C = 7.376444421930428`,
`|λ| < 0.5207046554`); that numerical statement is not formalized. **Scope.** Real algebra only; nothing
here proves `m ≥ c`, the continuum lift, a residual tail bound, or RH/GRH.
-/

namespace GppPoleParameterBudget

theorem pole_lambda_square_identity (a b d lam : ℝ) :
    (d + 1 / 2) * (a - 2 * b * lam + (d + 1 / 2) * lam ^ 2) =
      (d + 1 / 2) * a - b ^ 2 + ((d + 1 / 2) * lam - b) ^ 2 := by
  ring

theorem pole_lambda_lower_bound (a b d lam : ℝ) :
    (d + 1 / 2) * a - b ^ 2 ≤
      (d + 1 / 2) * (a - 2 * b * lam + (d + 1 / 2) * lam ^ 2) := by
  rw [pole_lambda_square_identity]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem necessary_pole_lambda_budget
    (C β lam : ℝ) (hC : 0 < C) (hβ : 0 ≤ β)
    (hmargin : C * (β + lam ^ 2 / 2) < 1) :
    C * lam ^ 2 < 2 := by
  have hprod : 0 ≤ C * β := mul_nonneg (le_of_lt hC) hβ
  nlinarith

end GppPoleParameterBudget
