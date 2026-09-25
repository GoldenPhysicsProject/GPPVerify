import Mathlib.Tactic

/-!
# Arithmetic Hodge-index boundary core

This module formalizes the exact algebraic content of the current CCM/Hodge-index
interpretation without assuming RH and without inventing a geometric surface.

For a real vector space V, a linear functional degree : V → ℝ plays the role of the
two trivial/pole classes after one hyperbolic direction has been quotiented. The
load-bearing Hodge-index statement is simply:

  every primitive vector (degree x = 0) has nonnegative non-pole energy.

That hypothesis immediately implies that two genuinely independent negative directions
cannot survive: the degree-weighted cross-combination of any two vectors is primitive.
The second half records the corresponding Castelnuovo/pole closure: a quadratic lower
bound in the degree direction is exactly what is needed for the positive pole correction
to make the completed form nonnegative.

No concrete CCM positivity statement is assumed or proved here.
-/

namespace GppWeilParity

/-- A negative-energy vector cannot be primitive if the form is nonnegative on the
primitive hyperplane. -/
theorem negative_vector_has_nonzero_degree
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (degree : V →ₗ[ℝ] ℝ) (A : V → ℝ)
    (hprimitive : ∀ x, degree x = 0 → 0 ≤ A x)
    {x : V} (hx : A x < 0) :
    degree x ≠ 0 := by
  intro hdeg
  exact (not_lt_of_ge (hprimitive x hdeg)) hx

/-- The degree-weighted cross-combination of two states is always primitive. -/
theorem degree_cross_combination_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (degree : V →ₗ[ℝ] ℝ) (x y : V) :
    degree ((degree y) • x - (degree x) • y) = 0 := by
  simp
  ring

/-- Abstract Hodge-index obstruction. If the non-pole form is nonnegative on the
primitive hyperplane, then the degree-weighted cross-combination of any two states has
nonnegative energy.

Thus a two-dimensional subspace on which the form were strictly negative would have to
collapse in the degree direction. This is the algebraic core of negative index at most
one; no eigenvalue machinery is required for this implication. -/
theorem primitive_cross_combination_nonneg
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (degree : V →ₗ[ℝ] ℝ) (A : V → ℝ)
    (hprimitive : ∀ x, degree x = 0 → 0 ≤ A x)
    (x y : V) :
    0 ≤ A ((degree y) • x - (degree x) • y) := by
  apply hprimitive
  exact degree_cross_combination_eq_zero degree x y

/-- A quantitative Hodge-index lower bound in the unique degree direction. -/
def HodgeIndexLowerBound
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (degree : V →ₗ[ℝ] ℝ) (A : V → ℝ) (κ : ℝ) : Prop :=
  ∀ x, -κ * (degree x) ^ 2 ≤ A x

/-- Castelnuovo/pole closure. A Hodge-index lower bound
A x ≥ -κ (degree x)^2 is precisely enough for the pole correction
+κ (degree x)^2 to make the completed energy nonnegative. -/
theorem completed_nonneg_of_hodgeIndexLowerBound
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (degree : V →ₗ[ℝ] ℝ) (A : V → ℝ) (κ : ℝ)
    (hA : HodgeIndexLowerBound degree A κ) :
    ∀ x, 0 ≤ A x + κ * (degree x) ^ 2 := by
  intro x
  have hx := hA x
  linarith

/-- Conversely, nonnegativity after the pole correction is exactly the same scalar lower
bound on the non-pole form. -/
theorem hodgeIndexLowerBound_of_completed_nonneg
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (degree : V →ₗ[ℝ] ℝ) (A : V → ℝ) (κ : ℝ)
    (hQ : ∀ x, 0 ≤ A x + κ * (degree x) ^ 2) :
    HodgeIndexLowerBound degree A κ := by
  intro x
  have hx := hQ x
  linarith

/-- The two formulations are equivalent pointwise. -/
theorem hodgeIndexLowerBound_iff_completed_nonneg
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (degree : V →ₗ[ℝ] ℝ) (A : V → ℝ) (κ : ℝ) :
    HodgeIndexLowerBound degree A κ ↔
      ∀ x, 0 ≤ A x + κ * (degree x) ^ 2 := by
  constructor
  · exact completed_nonneg_of_hodgeIndexLowerBound degree A κ
  · exact hodgeIndexLowerBound_of_completed_nonneg degree A κ

/-- Any quantitative Hodge-index lower bound automatically contains primitive positivity:
on ker degree the defect term vanishes. -/
theorem primitive_nonneg_of_hodgeIndexLowerBound
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (degree : V →ₗ[ℝ] ℝ) (A : V → ℝ) (κ : ℝ)
    (hA : HodgeIndexLowerBound degree A κ)
    {x : V} (hx : degree x = 0) :
    0 ≤ A x := by
  have h := hA x
  rw [hx] at h
  norm_num at h
  exact h

/-- Subexponential Hodge defect version. If the non-pole form is bounded below by a
single degree-square defect plus a remainder E, then the pole-corrected form is bounded
below by -E. This is the exact form needed by the fixed-window theorem, where a
subexponential E(L) already suffices for RH. -/
theorem completed_semibounded_of_hodge_defect
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (degree : V →ₗ[ℝ] ℝ) (A : V → ℝ) (κ E : ℝ)
    (hA : ∀ x, -κ * (degree x) ^ 2 - E ≤ A x) :
    ∀ x, -E ≤ A x + κ * (degree x) ^ 2 := by
  intro x
  have hx := hA x
  linarith

end GppWeilParity
