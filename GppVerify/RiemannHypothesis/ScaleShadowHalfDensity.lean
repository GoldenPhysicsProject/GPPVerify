import GppVerify.RiemannHypothesis.ScaleMassDiagnostic
import Mathlib.Tactic

/-!
# Shadow symmetry of the half-density dilation character

For

  chi_s(a) = exp(log(a) * (s - 1/2)),

the shadow involution `s -> 1-s` negates the centered exponent. Hence it sends the
multiplicative dilation character to its reciprocal. Together with
`GppScaleMass.critical_line_iff_dilation_unitary`, this is the exact algebraic skeleton
behind the principal-series statement: on the unitary locus the shadow is the inverse
character, and therefore (for unit-modulus characters) the Hermitian conjugate character.

No zeta-zero statement is used or implied.
-/

namespace GppScaleShadow

open Complex
open GppScaleMass

/-- Shadow negates the half-density-centered exponent. -/
lemma shadow_centered_exponent (s : ℂ) :
    (1 - s) - (1 / 2 : ℂ) = -(s - (1 / 2 : ℂ)) := by
  ring

/-- The shadow character is exactly the reciprocal dilation character. -/
theorem dilationCharacter_shadow_eq_inv (s : ℂ) (a : ℝ) :
    dilationCharacter (1 - s) a = (dilationCharacter s a)⁻¹ := by
  unfold dilationCharacter
  rw [shadow_centered_exponent]
  rw [mul_neg, Complex.exp_neg]

/-- Applying shadow twice returns the original character. -/
theorem dilationCharacter_shadow_involution (s : ℂ) (a : ℝ) :
    dilationCharacter (1 - (1 - s)) a = dilationCharacter s a := by
  ring_nf

/-- At a nontrivial positive scale, the critical line is exactly the locus on which
    the character is unitary; on that same locus shadow acts by inversion. -/
theorem critical_line_iff_unitary_with_shadow {s : ℂ} {a : ℝ}
    (ha : 0 < a) (ha1 : a ≠ 1) :
    s.re = 1 / 2 ↔
      (‖dilationCharacter s a‖ = 1 ∧
       dilationCharacter (1 - s) a = (dilationCharacter s a)⁻¹) := by
  constructor
  · intro hs
    exact ⟨GppScaleMass.critical_line_dilation_unitary hs a,
      dilationCharacter_shadow_eq_inv s a⟩
  · intro h
    exact GppScaleMass.critical_line_of_dilation_unitary ha ha1 h.1

end GppScaleShadow

#print axioms GppScaleShadow.dilationCharacter_shadow_eq_inv
#print axioms GppScaleShadow.dilationCharacter_shadow_involution
#print axioms GppScaleShadow.critical_line_iff_unitary_with_shadow
