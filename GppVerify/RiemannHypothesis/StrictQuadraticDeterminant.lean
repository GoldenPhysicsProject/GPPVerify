import Mathlib.Tactic

/-!
# Strict positive quadratic forms force positive 2x2 determinant

This is the algebraic bridge needed to turn a strict two-observable Fisher
quadratic-form theorem into strict positivity of its covariance determinant.
For

  q(a,b) = A a^2 + 2 B a b + C b^2,

strict positivity on every nonzero coefficient pair implies both `A > 0` and
`A*C-B^2 > 0`.  The determinant step is constructive: evaluate first at `(1,0)`
and then at `(-B,A)`, where the quadratic form is

  q(-B,A) = A * (A*C-B^2).

No spectral, probabilistic, or finite-support assumption enters this lemma.
-/

namespace GppStrictQuadraticDeterminant

/-- A strictly positive real binary quadratic form has strictly positive Gram
determinant. -/
theorem det_pos_of_quadratic_pos
    (A B C : ℝ)
    (hpos : ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 →
      0 < A * a ^ 2 + 2 * B * a * b + C * b ^ 2) :
    0 < A * C - B ^ 2 := by
  have hAq := hpos 1 0 (Or.inl one_ne_zero)
  have hA : 0 < A := by
    simpa using hAq
  have hpair : (-B : ℝ) ≠ 0 ∨ A ≠ 0 :=
    Or.inr (ne_of_gt hA)
  have hdetq := hpos (-B) A hpair
  have hid :
      A * (-B) ^ 2 + 2 * B * (-B) * A + C * A ^ 2 =
        A * (A * C - B ^ 2) := by
    ring
  rw [hid] at hdetq
  rcases (mul_pos_iff.mp hdetq) with hsame | hsame
  · exact hsame.2
  · exact False.elim ((not_lt_of_ge hA.le) hsame.1)

end GppStrictQuadraticDeterminant

#print axioms GppStrictQuadraticDeterminant.det_pos_of_quadratic_pos
