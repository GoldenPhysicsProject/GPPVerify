import GppVerify.RiemannHypothesis.ScaleMassDiagnostic
import Mathlib.Tactic

/-!
# Shadow symmetry of the half-density dilation character

For

  chi_s(a) = exp(log(a) * (s - 1/2)),

the shadow involution `s -> 1-s` negates the centered exponent. Hence it sends the
multiplicative dilation character to its reciprocal. Together with the exact
critical-line unitarity statements from `ScaleMassDiagnostic`, this is the algebraic
skeleton behind the principal-series statement: on the unitary locus the shadow is the
inverse character, and therefore the Hermitian conjugate character.

No zeta-zero statement is used or implied.
-/

namespace GppScaleShadow

open Complex
open GppScaleMass

/-- Project celestial dictionary from the Mellin coordinate to scalar dimension. -/
noncomputable def celestialDelta (s : ℂ) : ℂ := 2 * s

/-- Shadow negates the half-density-centered exponent. -/
lemma shadow_centered_exponent (s : ℂ) :
    (1 - s) - (1 / 2 : ℂ) = -(s - (1 / 2 : ℂ)) := by
  ring

/-- The project dictionary `Delta = 2s` exactly intertwines the Riemann reflection
`s -> 1-s` with the scalar celestial shadow `Delta -> 2-Delta`. -/
theorem celestialDelta_shadow (s : ℂ) :
    celestialDelta (1 - s) = 2 - celestialDelta s := by
  unfold celestialDelta
  ring

/-- The Riemann critical line maps exactly to the scalar celestial principal line
`Re Delta = 1`. -/
theorem celestialDelta_re_eq_one_iff (s : ℂ) :
    (celestialDelta s).re = 1 ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have h' : 2 * s.re = 1 := by
      simpa [celestialDelta, Complex.mul_re] using h
    linarith
  · intro h
    have h' : 2 * s.re = 1 := by linarith
    simpa [celestialDelta, Complex.mul_re] using h'

/-- On the critical line, celestial shadow is complex conjugation after `Delta=2s`. -/
theorem celestialDelta_shadow_eq_conj {s : ℂ} (hs : s.re = 1 / 2) :
    2 - celestialDelta s = (starRingEnd ℂ) (celestialDelta s) := by
  apply Complex.ext
  · simp [celestialDelta, hs]
    norm_num
  · simp [celestialDelta]

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

/-- On the critical line, complex conjugation of the spectral parameter is exactly
shadow: `star s = 1 - s`. -/
theorem conj_eq_shadow_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    (starRingEnd ℂ) s = 1 - s := by
  apply Complex.ext
  · simp [hs]
    norm_num
  · simp

/-- A complex number of norm one has reciprocal equal to its Hermitian conjugate. -/
lemma inv_eq_star_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) :
    z⁻¹ = (starRingEnd ℂ) z := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
  simp

/-- On the critical line, the shadow dilation character is the Hermitian conjugate
of the original character. -/
theorem dilationCharacter_shadow_eq_conj {s : ℂ} (hs : s.re = 1 / 2) (a : ℝ) :
    dilationCharacter (1 - s) a = (starRingEnd ℂ) (dilationCharacter s a) := by
  rw [dilationCharacter_shadow_eq_inv]
  have hunit : ‖dilationCharacter s a‖ = 1 :=
    critical_line_dilation_unitary hs a
  exact inv_eq_star_of_norm_one hunit

/-- Exact principal-series package: the critical line is equivalent to unitarity of the
half-density dilation character at every real scale, while shadow acts there as Hermitian
conjugation.  The reverse implication uses the nontrivial positive scale `a = 2`. -/
theorem critical_line_iff_unitary_with_shadow (s : ℂ) :
    s.re = 1 / 2 ↔
      (∀ a : ℝ, ‖dilationCharacter s a‖ = 1) ∧
      (∀ a : ℝ, dilationCharacter (1 - s) a =
        (starRingEnd ℂ) (dilationCharacter s a)) := by
  constructor
  · intro hs
    constructor
    · exact fun a => critical_line_dilation_unitary hs a
    · exact fun a => dilationCharacter_shadow_eq_conj hs a
  · rintro ⟨hunit, _⟩
    have htwo : ‖dilationCharacter s 2‖ = 1 := hunit 2
    exact critical_line_of_dilation_unitary (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1) htwo

/-- Single-scale form: at a nontrivial positive scale, the critical line is exactly the
locus on which the character is unitary; on that same locus shadow acts by inversion. -/
theorem critical_line_iff_unitary_with_shadow_at_scale {s : ℂ} {a : ℝ}
    (ha : 0 < a) (ha1 : a ≠ 1) :
    s.re = 1 / 2 ↔
      (‖dilationCharacter s a‖ = 1 ∧
       dilationCharacter (1 - s) a = (dilationCharacter s a)⁻¹) := by
  constructor
  · intro hs
    exact ⟨critical_line_dilation_unitary hs a, dilationCharacter_shadow_eq_inv s a⟩
  · intro h
    exact critical_line_of_dilation_unitary ha ha1 h.1

end GppScaleShadow

#print axioms GppScaleShadow.celestialDelta_shadow
#print axioms GppScaleShadow.celestialDelta_re_eq_one_iff
#print axioms GppScaleShadow.celestialDelta_shadow_eq_conj
#print axioms GppScaleShadow.dilationCharacter_shadow_eq_inv
#print axioms GppScaleShadow.dilationCharacter_shadow_involution
#print axioms GppScaleShadow.conj_eq_shadow_of_re_eq_half
#print axioms GppScaleShadow.inv_eq_star_of_norm_one
#print axioms GppScaleShadow.dilationCharacter_shadow_eq_conj
#print axioms GppScaleShadow.critical_line_iff_unitary_with_shadow
