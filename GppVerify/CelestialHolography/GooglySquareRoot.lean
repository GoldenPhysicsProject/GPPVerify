import Mathlib.Tactic

/-!
# Square-root closure criterion for a googly operator

A recent useful structural target is to ask whether the linear googly operator `G`
is a square root of a complete orientation-reversal operator `R`:

  G^2 = R,   R^2 = id.

This file formalizes only the abstract algebraic consequences.  It does not assert
that the Penrose transform, Fourier/Radon transform, CPT, or the Yang--Mills/Einstein
googly operator satisfies these hypotheses.
-/

namespace GppGooglySquareRoot

/-- If `G^2 = R` and `R` is involutive, then `G` has fourth power equal to identity. -/
theorem fourth_power_of_square_root_involution
    {A : Type*} (G R : A -> A)
    (hG2 : ∀ x, G (G x) = R x)
    (hR2 : ∀ x, R (R x) = x) :
    ∀ x, G (G (G (G x))) = x := by
  intro x
  rw [hG2, hG2, hR2]

/-- If `G^2 = R`, then `G` commutes with `R` automatically. -/
theorem square_root_commutes_with_square
    {A : Type*} (G R : A -> A)
    (hG2 : ∀ x, G (G x) = R x) :
    ∀ x, G (R x) = R (G x) := by
  intro x
  rw [← hG2, ← hG2]

/-- If the orientation reversal is nontrivial at `x`, a square-root googly operator
cannot already square to identity there. -/
theorem square_not_identity_when_orientation_nontrivial
    {A : Type*} (G R : A -> A)
    (hG2 : ∀ x, G (G x) = R x)
    (x : A) (hRx : R x ≠ x) :
    G (G x) ≠ x := by
  rw [hG2]
  exact hRx

/-- Conversely, if `G` is itself involutive everywhere and also satisfies `G^2=R`,
then `R` must be the identity.  Thus a genuinely nontrivial orientation reversal
requires an order-four lift rather than an involutive lift. -/
theorem involutive_square_root_forces_trivial_orientation
    {A : Type*} (G R : A -> A)
    (hG2 : ∀ x, G (G x) = R x)
    (hGinv : ∀ x, G (G x) = x) :
    ∀ x, R x = x := by
  intro x
  rw [← hG2]
  exact hGinv x

/-- Exact-order-four witness criterion: if `R x ≠ x`, then the orbit of `x` under
`G` cannot close after two steps, while four steps always close. -/
theorem nontrivial_orientation_gives_four_step_closure
    {A : Type*} (G R : A -> A)
    (hG2 : ∀ x, G (G x) = R x)
    (hR2 : ∀ x, R (R x) = x)
    (x : A) (hRx : R x ≠ x) :
    G (G x) ≠ x ∧ G (G (G (G x))) = x := by
  exact ⟨square_not_identity_when_orientation_nontrivial G R hG2 x hRx,
         fourth_power_of_square_root_involution G R hG2 hR2 x⟩

end GppGooglySquareRoot
