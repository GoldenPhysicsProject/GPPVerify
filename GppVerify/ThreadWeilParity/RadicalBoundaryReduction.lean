import Mathlib

/-!
# Radical boundary reduction for the localized Weil form

This file formalizes the algebraic spine of the current CCM/Weil boundary program.

It deliberately does **not** claim the missing analytic input.  In particular it does not
construct a radical continuation, a co-Poisson boundary transform, or prove positivity of
the prime--Archimedean form.

What it does prove, without axioms or `sorry`, is:

* a symmetric additive pairing annihilating a global radical element gives equality of
  interior and exterior energies;
* subtracting a rank-one pole channel is nonnegative exactly when the corresponding sharp
  trace inequality holds;
* any boundary transform dominated by a positive bulk energy and satisfying the sharp
  trace estimate closes that rank-one channel.

These are the exact finite/algebraic implications used by the current RH program.
-/

namespace GppWeilParity

/--
If `r = g + h` is radical against both pieces `g` and `h` for a symmetric pairing
that is additive in its first argument, then the interior and exterior self-energies agree.

This is the abstract algebra behind
`Q_W(P_L r, P_L r) = Q_W((1-P_L)r, (1-P_L)r)`.
-/
theorem interior_eq_exterior_of_radical
    {V : Type*} [AddCommGroup V]
    (B : V → V → ℝ)
    (hadd : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsymm : ∀ x y, B x y = B y x)
    {g h : V}
    (hg : B (g + h) g = 0)
    (hh : B (g + h) h = 0) :
    B g g = B h h := by
  rw [hadd g h g] at hg
  rw [hadd g h h] at hh
  rw [hsymm h g] at hg
  linarith

/--
A quadratic form with one negative rank-one pole channel is nonnegative exactly when the
corresponding sharp trace inequality holds pointwise.
-/
theorem rankOne_sub_nonneg_iff
    {V : Type*} (A : V → ℝ) (ell : V → ℝ) :
    (∀ x, 0 ≤ A x - (ell x) ^ 2 / 2) ↔
      ∀ x, (ell x) ^ 2 ≤ 2 * A x := by
  constructor
  · intro h x
    have hx := h x
    nlinarith
  · intro h x
    have hx := h x
    nlinarith

/--
The scalar core of the sharp half-line co-Poisson trace estimate: if a completed square is
nonnegative and equals `energy - boundary^2/2`, then
`boundary^2 ≤ 2*energy`.
-/
theorem sharp_trace_of_square_identity
    {energy square boundary : ℝ}
    (hsq : 0 ≤ square)
    (hid : square = energy - boundary ^ 2 / 2) :
    boundary ^ 2 ≤ 2 * energy := by
  nlinarith

/--
Abstract closure theorem for the odd pole channel.

If a transform `T` sends the finite state into a boundary space whose positive energy
`K` is dominated by the non-pole energy `A`, the pole functional is exactly the boundary
trace, and that trace obeys the sharp constant-two estimate, then
`A - ell^2/2` is nonnegative.

The still-open RH-strength input is the concrete construction of such a transform for the
full prime--Archimedean CCM form.
-/
theorem boundary_factorization_closes_rankOne
    {V W : Type*}
    (A : V → ℝ) (K : W → ℝ)
    (ell : V → ℝ) (trace : W → ℝ) (T : V → W)
    (hdom : ∀ x, K (T x) ≤ A x)
    (htrace : ∀ y, (trace y) ^ 2 ≤ 2 * K y)
    (hcompat : ∀ x, ell x = trace (T x)) :
    ∀ x, 0 ≤ A x - (ell x) ^ 2 / 2 := by
  intro x
  have hd := hdom x
  have ht := htrace (T x)
  rw [hcompat x]
  nlinarith

/--
A convenient equivalent form of the preceding theorem: under the same hypotheses the
sharp rank-one trace inequality follows directly.
-/
theorem boundary_factorization_trace_bound
    {V W : Type*}
    (A : V → ℝ) (K : W → ℝ)
    (ell : V → ℝ) (trace : W → ℝ) (T : V → W)
    (hdom : ∀ x, K (T x) ≤ A x)
    (htrace : ∀ y, (trace y) ^ 2 ≤ 2 * K y)
    (hcompat : ∀ x, ell x = trace (T x)) :
    ∀ x, (ell x) ^ 2 ≤ 2 * A x := by
  intro x
  have hd := hdom x
  have ht := htrace (T x)
  rw [hcompat x]
  nlinarith

end GppWeilParity
