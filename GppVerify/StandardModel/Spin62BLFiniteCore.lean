import Mathlib.Tactic

/-!
# Spin(6,2) four-lift / B-L finite core

Finite arithmetic and sign algebra accompanying Daniel Toupin,
"Which Way Is Forward?", v17.

The paper's Lie-group theorem uses the standard maximal-compact description
  (Spin(6) x Spin(2)) / diag Z2
and Spin(6) ~= SU(4).
This file formalizes the elementary core that is independent of any Lie-group API:

* an SU(3)-commuting diagonal traceless generator has weights (a,a,a,-3a);
* the primitive integer weights are (1,1,1,-3), all odd;
* simultaneous reversal of internal and transverse signs preserves their product;
* simultaneous reversal of an X-weight and transverse orientation preserves X*eta.

It does NOT formalize Spin(6,2), maximal compact subgroups, or representation
branching itself.
-/

namespace GppSpin62BLFiniteCore

/-- Tracelessness fixes the fourth color-centralizer weight. -/
theorem colorCentralizer_fourth_weight
    (a b : ℝ) (htrace : 3 * a + b = 0) :
    b = -3 * a := by
  linarith

/-- Primitive integer SU(4) color-centralizer weights. -/
def x1 : ℤ := 1
def x2 : ℤ := 1
def x3 : ℤ := 1
def x4 : ℤ := -3

/-- The primitive generator is traceless. -/
theorem primitive_generator_trace_zero :
    x1 + x2 + x3 + x4 = 0 := by
  norm_num [x1, x2, x3, x4]

/-- Every primitive fundamental weight is odd. -/
theorem primitive_generator_all_odd :
    Odd x1 ∧ Odd x2 ∧ Odd x3 ∧ Odd x4 := by
  norm_num [x1, x2, x3, x4, Odd]

/-- Relative chirality/orientation grading. -/
def alignment (g eta : ℤ) : ℤ := g * eta

/-- Reversing both signs preserves their relative product. -/
theorem diagonal_reversal_preserves_alignment
    (g eta : ℤ) :
    alignment (-g) (-eta) = alignment g eta := by
  simp [alignment]

/-- Reversing only the internal sign reverses the relative product. -/
theorem internal_half_flip_reverses_alignment
    (g eta : ℤ) :
    alignment (-g) eta = - alignment g eta := by
  simp [alignment]

/-- Relational X-orientation character. -/
def relationalX (X eta : ℤ) : ℤ := X * eta

/-- Complete conjugation X -> -X, eta -> -eta is relationally invisible. -/
theorem complete_conjugation_preserves_relationalX
    (X eta : ℤ) :
    relationalX (-X) (-eta) = relationalX X eta := by
  simp [relationalX]

/-- Charge conjugation at fixed observer orientation is visible. -/
theorem fixed_orientation_charge_flip
    (X eta : ℤ) :
    relationalX (-X) eta = - relationalX X eta := by
  simp [relationalX]

end GppSpin62BLFiniteCore
