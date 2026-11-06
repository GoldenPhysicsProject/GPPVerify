import GppVerify.RiemannHypothesis.WeilSupportLadder

/-!
# Rung 1 of the Weil support ladder: the first prime switches on

Requested by Daniel Toupin: build, without mentioning zeros, the step where
positivity has to survive a prime entering. `WeilSupportLadder` has rung 0
(support below `log 2`: no prime enters, the Weil form is its archimedean part).
This module is rung 1. For test functions supported in `[-L, L]` with
`L < log 3`, exactly one prime power is visible, `n = 2`, and

  `primeSide f = (log 2 / √2) * (f (log 2) + f (-log 2))`   (exact, no tail).

Consequently, on rung 1 the Weil form `arch - primeSide f` is nonnegative iff
`arch ≥ (log 2 / √2)(f(log 2) + f(-log 2))`: positivity at rung 1 is exactly a
single domination inequality of the archimedean part over the one prime kick
at `p = 2` (`weil_nonneg_iff_rung_one`), and it holds automatically whenever the
kick is nonpositive (`weil_nonneg_rung_one_of_kick_nonpos`). No zero of any
L-function appears. The archimedean inequality itself (the content of extending
Connes-Consani past `log 2`) is NOT proved here. No claim about RH.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.
-/

namespace GppWeilRungOne

open ArithmeticFunction GppWeilLadder

/-- The single prime kick visible on rung 1. -/
noncomputable def kickTwo (f : ℝ → ℝ) : ℝ :=
  (Real.log 2 / Real.sqrt 2) * (f (Real.log 2) + f (-(Real.log 2)))

/-- **Rung 1, exact.** With support below `log 3`, the prime side is the `p = 2` kick. -/
theorem primeSide_eq_kickTwo {f : ℝ → ℝ} {L : ℝ} (hf : HasSupportIn f L)
    (hL : L < Real.log 3) : primeSide f = kickTwo f := by
  have h3 : L < Real.log ((2 : ℕ) + 1) := by norm_num; exact hL
  rw [primeSide_eq_truncation hf h3]
  simp [Finset.sum_range_succ, vonMangoldt_apply_one,
    vonMangoldt_apply_prime Nat.prime_two, kickTwo]

/-- **Rung 1 positivity is exactly one domination inequality.** -/
theorem weil_nonneg_iff_rung_one {f : ℝ → ℝ} {L arch : ℝ} (hf : HasSupportIn f L)
    (hL : L < Real.log 3) : 0 ≤ arch - primeSide f ↔ kickTwo f ≤ arch := by
  rw [primeSide_eq_kickTwo hf hL, sub_nonneg]

/-- If the archimedean part is nonnegative and the `p = 2` kick is nonpositive,
the rung-1 Weil form is nonnegative. -/
theorem weil_nonneg_rung_one_of_kick_nonpos {f : ℝ → ℝ} {L arch : ℝ}
    (hf : HasSupportIn f L) (hL : L < Real.log 3) (harch : 0 ≤ arch)
    (hkick : f (Real.log 2) + f (-(Real.log 2)) ≤ 0) : 0 ≤ arch - primeSide f := by
  rw [weil_nonneg_iff_rung_one hf hL]
  have hc : 0 ≤ Real.log 2 / Real.sqrt 2 := by positivity
  unfold kickTwo
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hc hkick]

/-- The rung-1 class strictly contains rung 0: below `log 2` the kick vanishes. -/
theorem kickTwo_eq_zero_of_support_lt_log_two {f : ℝ → ℝ} {L : ℝ}
    (hf : HasSupportIn f L) (hL : L < Real.log 2) : kickTwo f = 0 := by
  have h3 : L < Real.log 3 := lt_trans hL (Real.log_lt_log (by norm_num) (by norm_num))
  rw [← primeSide_eq_kickTwo hf h3, primeSide_eq_zero_of_support_lt_log_two hf hL]

end GppWeilRungOne

#print axioms GppWeilRungOne.primeSide_eq_kickTwo
#print axioms GppWeilRungOne.weil_nonneg_iff_rung_one
