import Mathlib.Tactic

/-!
# Square-root closure criterion for an order-four lift

A useful structural target is an operator `G` whose square is a specified involution `R`:

  G^2 = R,   R^2 = id.

The algebra below is completely generic.  In particular, `R` must NOT be identified from
these theorems alone with four-orientation reversal, parity, time reversal, CPT, or any
other physical symmetry.  In the explicit Grassmannian/Klein construction developed in
neighboring modules, the relevant square is a conformal spacetime inversion; chirality
exchange and four-orientation reversal require additional Pin/Hodge data.

This file formalizes only the abstract consequences `G^4 = id`, commutation with the
square, and the exact-order-four witness criterion.  It does not assert that the Penrose
transform, Fourier/Radon transform, celestial shadow, CPT, or the Yang--Mills/Einstein
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

/-- If the involution is nontrivial at `x`, a square-root lift cannot already square to
identity there. -/
theorem square_not_identity_when_involution_nontrivial
    {A : Type*} (G R : A -> A)
    (hG2 : ∀ x, G (G x) = R x)
    (x : A) (hRx : R x ≠ x) :
    G (G x) ≠ x := by
  rw [hG2]
  exact hRx

/-- Backward-compatible theorem name.  The proof is algebraic and the argument `R` is a
generic involution; the name does not identify it physically with orientation reversal. -/
theorem square_not_identity_when_orientation_nontrivial
    {A : Type*} (G R : A -> A)
    (hG2 : ∀ x, G (G x) = R x)
    (x : A) (hRx : R x ≠ x) :
    G (G x) ≠ x :=
  square_not_identity_when_involution_nontrivial G R hG2 x hRx

/-- Conversely, if `G` is itself involutive everywhere and also satisfies `G^2=R`, then
`R` must be the identity.  Thus a genuinely nontrivial involution requires an order-four
lift rather than an involutive lift. -/
theorem involutive_square_root_forces_trivial_involution
    {A : Type*} (G R : A -> A)
    (hG2 : ∀ x, G (G x) = R x)
    (hGinv : ∀ x, G (G x) = x) :
    ∀ x, R x = x := by
  intro x
  rw [← hG2]
  exact hGinv x

/-- Backward-compatible theorem name with the same generic content. -/
theorem involutive_square_root_forces_trivial_orientation
    {A : Type*} (G R : A -> A)
    (hG2 : ∀ x, G (G x) = R x)
    (hGinv : ∀ x, G (G x) = x) :
    ∀ x, R x = x :=
  involutive_square_root_forces_trivial_involution G R hG2 hGinv

/-- Exact-order-four witness criterion: if `R x ≠ x`, then the orbit of `x` under `G`
cannot close after two steps, while four steps always close. -/
theorem nontrivial_involution_gives_four_step_closure
    {A : Type*} (G R : A -> A)
    (hG2 : ∀ x, G (G x) = R x)
    (hR2 : ∀ x, R (R x) = x)
    (x : A) (hRx : R x ≠ x) :
    G (G x) ≠ x ∧ G (G (G (G x))) = x := by
  exact ⟨square_not_identity_when_involution_nontrivial G R hG2 x hRx,
         fourth_power_of_square_root_involution G R hG2 hR2 x⟩

/-- Backward-compatible theorem name with the same generic content. -/
theorem nontrivial_orientation_gives_four_step_closure
    {A : Type*} (G R : A -> A)
    (hG2 : ∀ x, G (G x) = R x)
    (hR2 : ∀ x, R (R x) = x)
    (x : A) (hRx : R x ≠ x) :
    G (G x) ≠ x ∧ G (G (G (G x))) = x :=
  nontrivial_involution_gives_four_step_closure G R hG2 hR2 x hRx

end GppGooglySquareRoot
