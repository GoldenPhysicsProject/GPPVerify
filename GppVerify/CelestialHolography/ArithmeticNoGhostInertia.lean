import Mathlib.Tactic

/-!
# Arithmetic no-ghost obstruction: positive reweighting cannot remove a ghost

An off-critical zero quartet contributes, on the zero side of the arithmetic
heat Hankel kernel, an indefinite two-channel block of the schematic form

  2 (u ⊗ u - v ⊗ v).

A strictly positive scalar reweighting cannot turn such a block positive: the
negative channel remains negative.  Thus a positive Fisher/Gamma metric can
help define the ambient Hilbert structure, but by itself it cannot remove an
odd cohomology class.  A genuine quotient/cancellation (a no-ghost theorem) is
required.

This file formalizes the elementary algebraic obstruction only.  It does not
assert that an off-critical zero exists.
-/

namespace GppArithmeticNoGhost

/-- The model Lorentzian two-channel quadratic form. -/
def ghostForm (x y : ℝ) : ℝ := x^2 - y^2

/-- The odd channel is strictly negative. -/
theorem ghostForm_odd_negative : ghostForm 0 1 < 0 := by
  norm_num [ghostForm]

/-- Multiplying the entire form by a strictly positive weight preserves the
negative ghost direction. -/
theorem positive_scalar_weight_does_not_remove_ghost
    (w : ℝ) (hw : 0 < w) :
    w * ghostForm 0 1 < 0 := by
  simp [ghostForm, hw]

/-- Consequently no strictly positive scalar reweighting makes the model
quadratic form positive semidefinite on all two-channel states. -/
theorem no_positive_scalar_reweighting
    (w : ℝ) (hw : 0 < w) :
    ¬ (∀ x y : ℝ, 0 ≤ w * ghostForm x y) := by
  intro h
  have h01 := h 0 1
  have hneg := positive_scalar_weight_does_not_remove_ghost w hw
  linarith

/-- Even allowing separate strictly positive weights on the even and odd
squares leaves the pure odd direction negative. -/
theorem positive_diagonal_metric_does_not_remove_ghost
    (we wo : ℝ) (hwo : 0 < wo) :
    we * (0 : ℝ)^2 - wo * (1 : ℝ)^2 < 0 := by
  simp [hwo]

end GppArithmeticNoGhost

#print axioms GppArithmeticNoGhost.ghostForm_odd_negative
#print axioms GppArithmeticNoGhost.no_positive_scalar_reweighting
#print axioms GppArithmeticNoGhost.positive_diagonal_metric_does_not_remove_ghost
