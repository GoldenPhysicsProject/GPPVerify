import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-!
# Leading minors of a symmetric `3 × 3` form: positive definite or signature `(2, 1)`

Source: Codex, GPP-bridge PR #11 comment 6390445769 (Discovery2 PR #21, Arb-certified prime-site
signatures). Daniel Toupin / Golden Physics Project, with AI assistance from Codex (statement) and
Claude Code (formalization).

For the symmetric matrix `[[a, b, c], [b, d, e], [c, e, f]]` with quadratic form `Q`, put
`Δ₁ = a`, `Δ₂ = ad − b²` and `Δ₃ = det`.

* `ldl3_identity`: `a Δ₂ Q(x) = Δ₂ (a x₁ + b x₂ + c x₃)² + (Δ₂ x₂ + (ae − bc) x₃)² + a Δ₃ x₃²`,
  the explicit LDL / completing-the-square identity.
* `posDef_of_minors`: minor signs `(+, +, +)` make `Q` positive definite.
* `signature_two_one_of_minors`: minor signs `(+, +, −)` make `Q` positive definite on the plane
  `x₃ = 0` and strictly negative at an explicit vector, so by Sylvester's law of inertia its
  inertia is `(2+, 1−)`.

This is the exact implication behind Codex's certified `ζ` site `Q_3^-` (`(+, +, −)`, inertia
`(2, 1)`) versus `F_{1/4}` (`(+, +, +)`, inertia `(3, 0)`).

**Scope.** The general algebraic implication only. Plugging in the Arb-certified entry intervals
from Discovery2 #21 is not done here, and Sylvester's law of inertia itself is not formalized (the
two conclusions are stated directly). The site matrix is a finite prime-site contribution, not a
complete local height. No claim about RH or BSD.
-/

namespace GppSylvester3

/-- The quadratic form of `[[a, b, c], [b, d, e], [c, e, f]]`. -/
def Q (a b c d e f x₁ x₂ x₃ : ℝ) : ℝ :=
  a * x₁ ^ 2 + d * x₂ ^ 2 + f * x₃ ^ 2 + 2 * b * x₁ * x₂ + 2 * c * x₁ * x₃ + 2 * e * x₂ * x₃

/-- The second leading minor. -/
def Δ₂ (a b d : ℝ) : ℝ := a * d - b ^ 2

/-- The determinant. -/
def Δ₃ (a b c d e f : ℝ) : ℝ :=
  a * (d * f - e ^ 2) - b * (b * f - c * e) + c * (b * e - c * d)

/-- **LDL identity.** -/
theorem ldl3_identity (a b c d e f x₁ x₂ x₃ : ℝ) :
    a * Δ₂ a b d * Q a b c d e f x₁ x₂ x₃ =
      Δ₂ a b d * (a * x₁ + b * x₂ + c * x₃) ^ 2 + (Δ₂ a b d * x₂ + (a * e - b * c) * x₃) ^ 2
        + a * Δ₃ a b c d e f * x₃ ^ 2 := by
  unfold Δ₂ Δ₃ Q; ring

/-- **Minors `(+, +, +)`: positive definite.** -/
theorem posDef_of_minors {a b c d e f : ℝ} (h1 : 0 < a) (h2 : 0 < Δ₂ a b d)
    (h3 : 0 < Δ₃ a b c d e f) {x₁ x₂ x₃ : ℝ} (hx : x₁ ≠ 0 ∨ x₂ ≠ 0 ∨ x₃ ≠ 0) :
    0 < Q a b c d e f x₁ x₂ x₃ := by
  have hid := ldl3_identity a b c d e f x₁ x₂ x₃
  have hpos : 0 < a * Δ₂ a b d * Q a b c d e f x₁ x₂ x₃ := by
    rw [hid]
    rcases eq_or_ne x₃ 0 with h3' | h3'
    · subst h3'
      rcases eq_or_ne x₂ 0 with h2' | h2'
      · subst h2'
        have hx1 : x₁ ≠ 0 := by tauto
        have : 0 < (a * x₁) ^ 2 := by positivity
        simp only [mul_zero, add_zero, zero_pow two_ne_zero]
        nlinarith
      · have : 0 < (Δ₂ a b d * x₂) ^ 2 := by positivity
        simp only [mul_zero, add_zero, zero_pow two_ne_zero]
        nlinarith [sq_nonneg (a * x₁ + b * x₂)]
    · have : 0 < a * Δ₃ a b c d e f * x₃ ^ 2 := by positivity
      nlinarith [sq_nonneg (a * x₁ + b * x₂ + c * x₃),
        sq_nonneg (Δ₂ a b d * x₂ + (a * e - b * c) * x₃)]
  have hk : 0 < a * Δ₂ a b d := mul_pos h1 h2
  exact pos_of_mul_pos_right hpos hk.le

/-- **Minors `(+, +, −)`: positive on the plane `x₃ = 0`, negative at an explicit vector.** -/
theorem signature_two_one_of_minors {a b c d e f : ℝ} (h1 : 0 < a) (h2 : 0 < Δ₂ a b d)
    (h3 : Δ₃ a b c d e f < 0) :
    (∀ x₁ x₂ : ℝ, (x₁ ≠ 0 ∨ x₂ ≠ 0) → 0 < Q a b c d e f x₁ x₂ 0) ∧
      ∃ x₁ x₂ x₃ : ℝ, Q a b c d e f x₁ x₂ x₃ < 0 := by
  have hk : 0 < a * Δ₂ a b d := mul_pos h1 h2
  refine ⟨fun x₁ x₂ hx => ?_, ?_⟩
  · have hid := ldl3_identity a b c d e f x₁ x₂ 0
    have hpos : 0 < a * Δ₂ a b d * Q a b c d e f x₁ x₂ 0 := by
      rw [hid]
      simp only [mul_zero, add_zero, zero_pow two_ne_zero]
      rcases eq_or_ne x₂ 0 with h2' | h2'
      · subst h2'
        have hx1 : x₁ ≠ 0 := by tauto
        have : 0 < (a * x₁) ^ 2 := by positivity
        simp only [mul_zero, add_zero]
        nlinarith
      · have : 0 < (Δ₂ a b d * x₂) ^ 2 := by positivity
        nlinarith [sq_nonneg (a * x₁ + b * x₂)]
    exact pos_of_mul_pos_right hpos hk.le
  · set x₂ := -(a * e - b * c) / Δ₂ a b d with hx₂
    set x₁ := -(b * x₂ + c) / a with hx₁
    refine ⟨x₁, x₂, 1, ?_⟩
    have hid := ldl3_identity a b c d e f x₁ x₂ 1
    have e1 : a * x₁ + b * x₂ + c * 1 = 0 := by
      rw [hx₁]; field_simp; ring
    have e2 : Δ₂ a b d * x₂ + (a * e - b * c) * 1 = 0 := by
      rw [hx₂]; field_simp; ring
    rw [e1, e2] at hid
    have hneg : a * Δ₂ a b d * Q a b c d e f x₁ x₂ 1 < 0 := by
      rw [hid]; nlinarith
    by_contra hQ
    push Not at hQ
    have : 0 ≤ a * Δ₂ a b d * Q a b c d e f x₁ x₂ 1 := mul_nonneg hk.le hQ
    linarith

end GppSylvester3
