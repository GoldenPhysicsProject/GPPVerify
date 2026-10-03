import Mathlib.Tactic

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


/--
If a particular radical continuation has nonnegative exterior energy, then its interior
restriction has nonnegative energy as well.
-/
theorem interior_nonneg_of_radical_exterior_nonneg
    {V : Type*} [AddCommGroup V]
    (B : V → V → ℝ)
    (hadd : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsymm : ∀ x y, B x y = B y x)
    {g h : V}
    (hg : B (g + h) g = 0)
    (hh : B (g + h) h = 0)
    (hext : 0 ≤ B h h) :
    0 ≤ B g g := by
  have heq : B g g = B h h :=
    interior_eq_exterior_of_radical B hadd hsymm hg hh
  rw [heq]
  exact hext

/--
Surjective radical continuation plus exterior semiboundedness closes the localized form.

This is the exact algebraic version of the proposed arithmetic Hodge principle:
if every interior state extends to a global radical state whose exterior piece has
nonnegative Weil energy, then the localized Weil form is nonnegative.
-/
theorem localized_nonneg_of_radical_extensions
    {V : Type*} [AddCommGroup V]
    (B : V → V → ℝ)
    (hadd : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsymm : ∀ x y, B x y = B y x)
    (hext :
      ∀ g : V, ∃ h : V,
        B (g + h) g = 0 ∧
        B (g + h) h = 0 ∧
        0 ≤ B h h) :
    ∀ g : V, 0 ≤ B g g := by
  intro g
  obtain ⟨h, hg, hh, hpos⟩ := hext g
  exact interior_nonneg_of_radical_exterior_nonneg B hadd hsymm hg hh hpos

/--
A real-valued energy that can be approximated arbitrarily closely by nonnegative energies
is itself nonnegative.  This is the quantitative core needed to pass from *dense radical
restrictions* to positivity, without silently replacing density by surjectivity.
-/
theorem nonneg_of_arbitrarily_close_nonneg
    {V : Type*} (q : V → ℝ)
    (happrox :
      ∀ x : V, ∀ ε : ℝ, 0 < ε →
        ∃ y : V, 0 ≤ q y ∧ |q x - q y| < ε) :
    ∀ x : V, 0 ≤ q x := by
  intro x
  by_contra hx
  have hneg : q x < 0 := lt_of_not_ge hx
  have heps : 0 < -(q x) / 2 := by linarith
  obtain ⟨y, hy, hclose⟩ := happrox x (-(q x) / 2) heps
  have hleft := (abs_lt.mp hclose).1
  linarith

/--
Approximate radical continuation is enough: it suffices that every target energy can be
approximated arbitrarily closely by an interior piece of a radical state whose exterior
energy is nonnegative.

This is the honest finite-energy replacement for the stronger and generally false claim
that every window function has an *exact* radical continuation.
-/
theorem localized_nonneg_of_approximate_radical_extensions
    {V : Type*} [AddCommGroup V]
    (B : V → V → ℝ)
    (hadd : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsymm : ∀ x y, B x y = B y x)
    (happrox :
      ∀ g : V, ∀ ε : ℝ, 0 < ε →
        ∃ g' h : V,
          B (g' + h) g' = 0 ∧
          B (g' + h) h = 0 ∧
          0 ≤ B h h ∧
          |B g g - B g' g'| < ε) :
    ∀ g : V, 0 ≤ B g g := by
  apply nonneg_of_arbitrarily_close_nonneg (fun g => B g g)
  intro g ε hε
  obtain ⟨g', h, hg', hh, hext, hclose⟩ := happrox g ε hε
  refine ⟨g', ?_, hclose⟩
  exact interior_nonneg_of_radical_exterior_nonneg B hadd hsymm hg' hh hext

end GppWeilParity
