import GppVerify.RiemannHypothesis.TwoFacePoleSignature

/-!
# Rank-one positive compensation cannot remove a two-channel negative sector

Source: Daniel Toupin / Golden Physics Project two-face conformal boundary program,
Codex's 2026-10-14 shifted F_theta polar-signature discovery
(GPP-bridge work/codex/2026-10-14_two_face_pole_negative_index_multiscale.md),
and the independently checked GppTwoFacePoleSignature theorem on main.

The fake completed product F_theta has two linearly independent odd polar negative
directions, whereas zeta has one. In any basis diagonalizing a strictly negative
two-dimensional quadratic form, no single positive rank-one boundary correction
can make the whole plane positive.

This file proves that elementary no-masking statement with arbitrary positive
weights and arbitrary coupling coefficients, supplying an explicit nonzero
vector in the kernel of that coupling. It neither identifies the true signed
prime-Archimedean remainder as rank one nor proves RH.
-/

namespace GppShiftedPoleRankOneNoGo

/-- A weighted two-channel negative form plus an arbitrary rank-one compensation. -/
def residual (α β a b λ x y : ℝ) : ℝ :=
  λ * (a * x + b * y) ^ 2 - (α * x ^ 2 + β * y ^ 2)

/-- **Exact rank-one no-masking.** Any real linear coupling on a strictly
two-negative-direction plane has a nonzero kernel witness, along which the
original negative quadratic form survives regardless of compensation strength. -/
theorem one_channel_cannot_heal_two_negative_modes
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (a b λ : ℝ) :
    ∃ x y : ℝ,
      0 < α * x ^ 2 + β * y ^ 2 ∧
      a * x + b * y = 0 ∧
      residual α β a b λ x y < 0 := by
  by_cases hab : a = 0 ∧ b = 0
  · rcases hab with ⟨ha, hb⟩
    refine ⟨1, 0, ?_, ?_, ?_⟩
    · simpa using hα
    · simp [ha, hb]
    · simp [residual, ha, hb]
      nlinarith
  · have hnot : a ≠ 0 ∨ b ≠ 0 := by
      by_cases ha : a = 0
      · right
        intro hb
        exact hab ⟨ha, hb⟩
      · exact Or.inl ha
    have hweight : 0 < α * b ^ 2 + β * a ^ 2 := by
      rcases hnot with ha | hb
      · have ha2 : 0 < a ^ 2 := by positivity
        have hp : 0 < β * a ^ 2 := mul_pos hβ ha2
        nlinarith [mul_nonneg (le_of_lt hα) (sq_nonneg b)]
      · have hb2 : 0 < b ^ 2 := by positivity
        have hp : 0 < α * b ^ 2 := mul_pos hα hb2
        nlinarith [mul_nonneg (le_of_lt hβ) (sq_nonneg a)]
    refine ⟨b, -a, ?_, ?_, ?_⟩
    · nlinarith
    · ring
    · unfold residual
      have hc : a * b + b * (-a) = 0 := by ring
      rw [hc]
      nlinarith

end GppShiftedPoleRankOneNoGo
