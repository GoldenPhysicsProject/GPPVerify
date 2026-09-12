/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import GppVerify.Upstream.OrderOfGrowth
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Zeros of an entire function of finite order

If `f` is entire, `f 0 ≠ 0`, and `f` has order of growth at most `ρ`, then the number of zeros
of `f` in the disc of radius `r`, counted with multiplicity, is at most `A + B * r ^ (ρ + ε)`
for every `ε > 0`.

This is Jensen's inequality with the growth bound substituted for the maximum modulus. Mathlib
supplies the inequality as `AnalyticOnNhd.sum_divisor_le`; all this file does is choose
`R = 2 r`, so that `log (R / r) = log 2` is a constant, and read off the two constants.

It is the first half of the statement that unlocks Hadamard's theorem. The second half —
turning this counting bound into `Summable fun n => ‖a n‖ ^ (-s)` for `s > ρ`, which is exactly
the hypothesis `Complex.weierstrassProduct` takes — is a dyadic summation over this bound.

## Main results

* `Complex.HasOrderLE.sum_divisor_le` : `n(r) ≤ A + B * r ^ (ρ + ε)`.
-/

open Real Metric MeromorphicOn Set

namespace Complex

variable {f : ℂ → ℂ} {ρ : ℝ}

/-- **The zero counting function of an entire function of finite order grows polynomially.**
For every `ε > 0` there are constants `A` and `B ≥ 0` with

  `∑ᶠ u, divisor f (closedBall 0 r) u ≤ A + B * r ^ (ρ + ε)`

for all `r > 0`. Taking `R = 2 r` in Jensen's inequality makes the denominator `log (R / r)`
the constant `log 2`, and the growth bound turns the numerator `log (M / ‖f 0‖)` into
`log (C + 1) - log ‖f 0‖ + 2 ^ (ρ + ε) * r ^ (ρ + ε)`. -/
theorem HasOrderLE.sum_divisor_le (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hord : HasOrderLE f ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r →
      ((∑ᶠ u, divisor f (closedBall (0 : ℂ) r) u : ℤ) : ℝ) ≤ A + B * r ^ (ρ + ε) := by
  obtain ⟨C, hC, hbound⟩ := hord ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log (C + 1) - Real.log ‖f 0‖) / Real.log 2,
          2 ^ (ρ + ε) / Real.log 2, by positivity, fun r hr => ?_⟩
  have hr2 : (0 : ℝ) < 2 * r := by linarith
  set M : ℝ := (C + 1) * rexp ((2 * r) ^ (ρ + ε)) with hMdef
  have hexp1 : (1 : ℝ) ≤ rexp ((2 * r) ^ (ρ + ε)) :=
    Real.one_le_exp (rpow_nonneg hr2.le _)
  have hMge : 1 ≤ M := by rw [hMdef]; nlinarith
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hMge
  have hana : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |2 * r|) :=
    (analyticOnNhd_univ_iff_differentiable.2 hf).mono (Set.subset_univ _)
  have hrabs : |r| = r := abs_of_pos hr
  have hRabs : |2 * r| = 2 * r := abs_of_pos hr2
  have hfb : ∀ z ∈ sphere (0 : ℂ) |2 * r|, ‖f z‖ ≤ M := by
    intro z hz
    have hznorm : ‖z‖ = 2 * r := by
      rw [hRabs] at hz
      simpa using mem_sphere_zero_iff_norm.1 hz
    calc ‖f z‖ ≤ C * rexp (‖z‖ ^ (ρ + ε)) := hbound z
      _ ≤ M := by
          rw [hznorm, hMdef]
          nlinarith [Real.exp_pos ((2 * r) ^ (ρ + ε))]
  have hjensen := AnalyticOnNhd.sum_divisor_le (c := 0) (r := r) (R := 2 * r) (M := M)
    (by rw [hrabs]; exact hr) (by rw [hrabs, hRabs]; linarith) hMge hana h0 hfb
  rw [hrabs] at hjensen
  refine hjensen.trans_eq ?_
  have hratio : 2 * r / r = 2 := by field_simp
  have hf0 : 0 < ‖f 0‖ := norm_pos_iff.2 h0
  have hnum : Real.log (M / ‖f 0‖)
      = Real.log (C + 1) - Real.log ‖f 0‖ + 2 ^ (ρ + ε) * r ^ (ρ + ε) := by
    rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hf0), hMdef,
      Real.log_mul (by linarith) (Real.exp_ne_zero _), Real.log_exp,
      Real.mul_rpow (by norm_num) hr.le]
    ring
  rw [hratio, hnum]
  field_simp

end Complex
