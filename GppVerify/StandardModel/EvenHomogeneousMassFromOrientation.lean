import Mathlib.Tactic

/-!
# Even homogeneous mass magnitude is the absolute value of a signed orientation order parameter

Let `phi : R` be a signed order parameter whose sign labels two orientation/tetrad lifts.
Suppose a physical mass magnitude `m(phi)` obeys only two structural requirements:

1. branch blindness: `m(-phi)=m(phi)`;
2. positive scale covariance: `m(a phi)=a m(phi)` for every `a>=0`.

Then there is no functional freedom left:

    m(phi) = |phi| m(1).

Thus, if a signed first-order phase generator is linear in the order parameter,

    b(phi) = phi m(1),

its magnitude is exactly the physical mass and its square is branch independent.  At the
symmetric point `phi=0`, the mass magnitude vanishes automatically.

This is a pure functional-equation theorem.  It does not establish that Nature has such a
single order parameter; it shows what follows if branch symmetry and scale homogeneity are
the relevant premetric constraints.
-/

namespace GppEvenHomogeneousMassFromOrientation

/-- Structural assumptions imply absolute-value form. -/
theorem even_posHomogeneous_eq_abs_mul
    (m : ℝ → ℝ)
    (heven : ∀ x, m (-x) = m x)
    (hhom : ∀ a x, 0 ≤ a → m (a*x) = a*m x) :
    ∀ x, m x = |x| * m 1 := by
  intro x
  by_cases hx : 0 ≤ x
  · have h := hhom x 1 hx
    have habs : |x| = x := abs_of_nonneg hx
    simpa [habs] using h
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hpos : 0 ≤ -x := by linarith
    have h := hhom (-x) 1 hpos
    have hev := heven x
    have habs : |x| = -x := abs_of_neg hxneg
    rw [← hev]
    simpa [habs] using h

/-- In particular the symmetric point necessarily has zero mass. -/
theorem mass_zero_at_symmetric_point
    (m : ℝ → ℝ)
    (hhom : ∀ a x, 0 ≤ a → m (a*x) = a*m x) :
    m 0 = 0 := by
  have h := hhom 0 1 (by norm_num)
  simpa using h

/-- The canonical mass law determined by one positive normalization constant. -/
def massMagnitude (m0 phi : ℝ) : ℝ := |phi| * m0

/-- Signed first-order phase/mass generator. -/
def signedMass (m0 phi : ℝ) : ℝ := phi*m0

/-- Physical mass is even under branch reversal. -/
theorem massMagnitude_even (m0 phi : ℝ) :
    massMagnitude m0 (-phi) = massMagnitude m0 phi := by
  simp [massMagnitude]

/-- Signed first-order mass/phase is odd. -/
theorem signedMass_odd (m0 phi : ℝ) :
    signedMass m0 (-phi) = -signedMass m0 phi := by
  ring

/-- Signed and physical mass have identical squares. -/
theorem signedMass_sq_eq_massMagnitude_sq (m0 phi : ℝ) :
    (signedMass m0 phi)^2 = (massMagnitude m0 phi)^2 := by
  simp [signedMass, massMagnitude, sq_abs]
  ring

/-- If the normalization is nonnegative, the resulting physical mass is nonnegative. -/
theorem massMagnitude_nonnegative (m0 phi : ℝ) (hm0 : 0 ≤ m0) :
    0 ≤ massMagnitude m0 phi := by
  exact mul_nonneg (abs_nonneg phi) hm0

/-- Both signed and physical mass vanish at the branch point. -/
theorem branch_point_massless (m0 : ℝ) :
    signedMass m0 0 = 0 ∧ massMagnitude m0 0 = 0 := by
  simp [signedMass, massMagnitude]

end GppEvenHomogeneousMassFromOrientation
