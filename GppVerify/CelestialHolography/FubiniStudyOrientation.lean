import GppVerify.CelestialHolography.FubiniStudyAntipodal
import Mathlib.Tactic

/-!
# Fubini–Study antipodal: measure positive, oriented 2-form negative

Daniel Toupin's 2026-10-17 insight: "They're positives pointing the other way."
The *unsigned* Haar/FS probability density is invariant, whereas the
*oriented* FS two-form is anti-invariant under the anti-holomorphic antipode.

The actual Weil polar cross-pair admits an exact even-minus-odd
decomposition. Orientation explains its sign; it does NOT prove Weil
positivity, which needs compensation by true prime/gamma energy.
-/

namespace GppFSOrientation

open GppFubiniStudy

/-- The antipodal map has strictly negative real Jacobian determinant
at every nonzero complex point, expressed in r=|z|²>0 coordinates. -/
theorem antipodal_jacobian_negative (r : ℝ) (hr : 0 < r) :
    -(1 / r ^ 2) < 0 := by
  have h : (0 : ℝ) < r ^ 2 := sq_pos_of_pos hr
  have hdiv : (0 : ℝ) < 1 / r ^ 2 := one_div_pos.mpr h
  linarith

/-- The corrected existing theorem concerns the POSITIVE (unsigned)
FS measure, including the absolute Jacobian. -/
theorem antipodal_unsigned_measure_invariant (r : ℝ) (hr : 0 < r) :
    fsDensity r⁻¹ * (1 / r ^ 2) = fsDensity r :=
  fs_measure_antipodal_invariant r hr

/-- Oriented FS two-forms change sign: pullback omega = -omega.
This follows from the signed, not absolute, Jacobian. -/
theorem antipodal_oriented_form_anti_invariant (r : ℝ) (hr : 0 < r) :
    fsDensity r⁻¹ * (-(1 / r ^ 2)) = -fsDensity r := by
  calc
    fsDensity r⁻¹ * (-(1 / r ^ 2)) =
        -(fsDensity r⁻¹ * (1 / r ^ 2)) := by ring
    _ = -fsDensity r := by rw [fs_measure_antipodal_invariant r hr]

/-- The exact Riemann/Weil polar cross-pair is a positive oriented
even-channel square MINUS a positive reversed odd-channel square.
The a-variables are real/imaginary parts of ell_+, b of ell_-. -/
theorem weil_pole_even_minus_odd (ar ai br bi : ℝ) :
    ((ar + br) ^ 2 + (ai + bi) ^ 2) / 2 -
      ((ar - br) ^ 2 + (ai - bi) ^ 2) / 2 =
        2 * (ar * br + ai * bi) := by
  ring

/-- A reversed channel has a strictly negative signed polar
contribution unless it vanishes. This is a counterexample to simply
identifying orientation covariance with ordinary Weil positivity. -/
theorem opposite_orientation_pole_negative (ar ai : ℝ)
    (h : ar ≠ 0 ∨ ai ≠ 0) :
    2 * (ar * (-ar) + ai * (-ai)) < 0 := by
  have hs : 0 < ar ^ 2 + ai ^ 2 := by
    rcases h with ha | hb
    · have : 0 < ar ^ 2 := sq_pos_of_ne_zero ha
      nlinarith [sq_nonneg ai]
    · have : 0 < ai ^ 2 := sq_pos_of_ne_zero hb
      nlinarith [sq_nonneg ar]
  nlinarith

end GppFSOrientation
