import GppVerify.RiemannHypothesis.FunctionalEquation
import GppVerify.RiemannHypothesis.ScaleShadowHalfDensity
import Mathlib.Tactic

/-!
# Centered xi and the half-density sign involution

Write `w = s - 1/2`.  Then both structures relevant to the critical line use the same
literal involution `w -> -w`:

* Riemann's functional equation becomes evenness of `Xi_c(w) = xi(1/2+w)`;
* the half-density dilation character becomes `exp(log(a)*w)`, and shadow sends it to
  the reciprocal character at `-w`.

This file proves only those exact algebraic identities.  No zero-location claim is made.
-/

namespace GppCenteredXi

open Complex
open GppFE
open GppScaleMass
open GppScaleShadow

/-- Riemann xi in the variable centered at the critical line. -/
noncomputable def centeredXi (w : ℂ) : ℂ :=
  riemannXi ((1 / 2 : ℂ) + w)

/-- In centered coordinates the functional equation is literal evenness. -/
theorem centeredXi_even (w : ℂ) : centeredXi w = centeredXi (-w) := by
  unfold centeredXi riemannXi
  rw [show (1 / 2 : ℂ) - w = 1 - ((1 / 2 : ℂ) + w) by ring]
  rw [completedRiemannZeta_one_sub]
  ring

/-- Zeros of centered xi occur in sign-reflected pairs. -/
theorem centeredXi_zero_neg {w : ℂ} (h : centeredXi w = 0) :
    centeredXi (-w) = 0 := by
  rw [← centeredXi_even w]
  exact h

/-- The half-density dilation character is just the exponential of the centered variable. -/
theorem dilationCharacter_centered (w : ℂ) (a : ℝ) :
    dilationCharacter ((1 / 2 : ℂ) + w) a =
      Complex.exp ((Real.log a : ℂ) * w) := by
  unfold dilationCharacter
  congr 1
  ring

/-- Shadow on `s=1/2+w` is exactly sign reversal `w -> -w`. -/
lemma shadow_centered_coordinate (w : ℂ) :
    1 - ((1 / 2 : ℂ) + w) = (1 / 2 : ℂ) - w := by
  ring

/-- The critical line in `s` is the imaginary axis in the centered coordinate `w`. -/
theorem critical_line_iff_centered_re_zero (w : ℂ) :
    (((1 / 2 : ℂ) + w).re = 1 / 2) ↔ w.re = 0 := by
  simp

end GppCenteredXi

#print axioms GppCenteredXi.centeredXi_even
#print axioms GppCenteredXi.centeredXi_zero_neg
#print axioms GppCenteredXi.dilationCharacter_centered
#print axioms GppCenteredXi.critical_line_iff_centered_re_zero
