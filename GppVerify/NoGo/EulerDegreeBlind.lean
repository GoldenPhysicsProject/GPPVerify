import GppVerify.RiemannHypothesis.SelectedPrimeCompensation

/-!
# No-go: the Euler-degree defect cannot see where zeros are

**Strategy refuted.** "Use the local moment defect `D_p = b₁² − b₂` of the prime-power log-derivative
coefficients to detect off-line zeros." (Codex, 2026-10-08, prime-moment defect note / PR #274.)

**Theorem (`defect_shift_invariant`).** For the two-channel radii `r₊ = p^{−1/2} t`, `r₋ = p^{−1/2}/t`
(any `t > 0`, which covers every shift `θ` via `t = p^θ`), the defect equals its value at `t = 1`.
`t = 1` is `ζ(s)²` — degree two, every zero on the line — while `t ≠ 1` is the shifted product
`ζ(s−θ)ζ(s+θ)` with off-line "zeros". Same `D_p`, so `D_p` detects Euler *degree*, not zero location.

**What the no-go leaves open (the hint).** The splitting witnesses `V_p = (r₊ − r₋)²` and
`H_p = V_p/p` do see the shift; a detector must use them (or the Archimedean completion), not `D_p`.
Positivity/negativity of `V_p` alone is still a local statement, not a zero-location theorem.
-/

namespace GppNoGo.EulerDegree

/-- The defect of the radii `(c·t, c/t)` is independent of `t`. -/
theorem defect_shift_invariant (c t : ℝ) (ht : t ≠ 0) :
    (c * t + c / t) ^ 2 - ((c * t) ^ 2 + (c / t) ^ 2)
      = (c * 1 + c / 1) ^ 2 - ((c * 1) ^ 2 + (c / 1) ^ 2) := by
  field_simp
  ring

/-- The splitting witness *does* see the shift: `(ct − c/t)² = 0` iff `t² = 1` (for `c ≠ 0`). -/
theorem splitting_sees_shift (c t : ℝ) (hc : c ≠ 0) (ht : t ≠ 0) :
    (c * t - c / t) ^ 2 = 0 ↔ t ^ 2 = 1 := by
  constructor
  · intro h
    have h1 : c * t - c / t = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h
    have h2 : c * (t ^ 2 - 1) = 0 := by
      field_simp at h1
      linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hc
    · linarith
  · intro h
    have : c * t - c / t = 0 := by
      field_simp
      linear_combination c * h
    rw [this]; ring

end GppNoGo.EulerDegree
