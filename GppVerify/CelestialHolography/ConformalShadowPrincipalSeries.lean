import GppVerify.RiemannHypothesis.ScaleShadowHalfDensity
import Mathlib.Tactic

/-!
# Conformal shadow and the principal-series line

For a scalar conformal weight `Delta` in real boundary dimension `d`, the shadow
involution is

  Delta |-> d - Delta.

Because `d` is real, this shadow equals Hermitian conjugation exactly on the
principal-series axis `Re Delta = d/2`.  The one-dimensional specialization is the
arithmetic reflection `s |-> 1-s`, whose principal line is `Re s = 1/2`.  Under the
project dictionary `Delta = 2s`, the same statement becomes the two-dimensional
celestial shadow `Delta |-> 2-Delta` with principal line `Re Delta = 1`.

The associated anti-linear reflection

  Delta |-> d - conj Delta

has the principal-series axis itself as its pointwise fixed set.  This makes precise
the distinction between holomorphic shadow (which pairs opposite spectral points)
and the anti-linear unitary-interface reflection (which fixes the admissible axis).

These are representation-theoretic identities only; no zeta-zero statement is used.
-/

namespace GppConformalShadowPrincipalSeries

open Complex
open GppScaleShadow

/-- Scalar conformal shadow in real boundary dimension `d`. -/
noncomputable def conformalShadow (d : ℝ) (Delta : ℂ) : ℂ := (d : ℂ) - Delta

/-- Conformal shadow is an involution. -/
theorem conformalShadow_involutive (d : ℝ) (Delta : ℂ) :
    conformalShadow d (conformalShadow d Delta) = Delta := by
  unfold conformalShadow
  ring

/-- The principal-series axis is exactly the locus where scalar shadow equals
Hermitian conjugation. -/
theorem conformalShadow_eq_conj_iff (d : ℝ) (Delta : ℂ) :
    conformalShadow d Delta = (starRingEnd ℂ) Delta ↔ Delta.re = d / 2 := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    simp [conformalShadow] at hr
    linarith
  · intro h
    apply Complex.ext
    · simp [conformalShadow]
      linarith
    · simp [conformalShadow]

/-- In one boundary dimension, the conformal shadow is literally the arithmetic
reflection `s |-> 1-s`. -/
theorem one_dimensional_shadow_eq_arithmetic (s : ℂ) :
    conformalShadow 1 s = 1 - s := by
  simp [conformalShadow]

/-- Consequently, the one-dimensional shadow is Hermitian conjugation exactly on the
Riemann critical line. -/
theorem one_dimensional_shadow_eq_conj_iff (s : ℂ) :
    conformalShadow 1 s = (starRingEnd ℂ) s ↔ s.re = 1 / 2 := by
  simpa using conformalShadow_eq_conj_iff 1 s

/-- Under `Delta = 2s`, arithmetic shadow is exactly the two-dimensional celestial
shadow. -/
theorem doubled_arithmetic_shadow_eq_two_dimensional (s : ℂ) :
    celestialDelta (1 - s) = conformalShadow 2 (celestialDelta s) := by
  rw [celestialDelta_shadow]
  simp [conformalShadow]

/-- Under `Delta = 2s`, the Riemann critical line is exactly the `d=2` celestial
principal-series line `Re Delta = 1`. -/
theorem critical_line_iff_two_dimensional_principal (s : ℂ) :
    s.re = 1 / 2 ↔ (celestialDelta s).re = 2 / 2 := by
  rw [show (2 : ℝ) / 2 = 1 by norm_num]
  exact (celestialDelta_re_eq_one_iff s).symm

/-- Anti-linear reflection associated with scalar shadow.  Unlike holomorphic shadow,
this operation fixes the unitary principal-series axis pointwise. -/
noncomputable def antiLinearShadow (d : ℝ) (Delta : ℂ) : ℂ :=
  (d : ℂ) - (starRingEnd ℂ) Delta

/-- The anti-linear shadow reflection is an involution. -/
theorem antiLinearShadow_involutive (d : ℝ) (Delta : ℂ) :
    antiLinearShadow d (antiLinearShadow d Delta) = Delta := by
  apply Complex.ext <;> simp [antiLinearShadow] <;> ring

/-- The fixed set of the anti-linear reflection is exactly `Re Delta = d/2`. -/
theorem antiLinearShadow_fixed_iff (d : ℝ) (Delta : ℂ) :
    antiLinearShadow d Delta = Delta ↔ Delta.re = d / 2 := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    simp [antiLinearShadow] at hr
    linarith
  · intro h
    apply Complex.ext
    · simp [antiLinearShadow]
      linarith
    · simp [antiLinearShadow]

/-- Arithmetic anti-linear reflection `s |-> 1-conj(s)` fixes exactly the critical
line `Re s = 1/2`. -/
theorem arithmetic_antiLinearShadow_fixed_iff (s : ℂ) :
    antiLinearShadow 1 s = s ↔ s.re = 1 / 2 := by
  simpa using antiLinearShadow_fixed_iff 1 s

/-- Celestial anti-linear reflection `Delta |-> 2-conj(Delta)` fixes exactly the
scalar principal-series axis `Re Delta = 1`. -/
theorem celestial_antiLinearShadow_fixed_iff (Delta : ℂ) :
    antiLinearShadow 2 Delta = Delta ↔ Delta.re = 1 := by
  simpa using antiLinearShadow_fixed_iff 2 Delta

/-- The scale dictionary `Delta = 2s` intertwines the arithmetic and celestial
anti-linear reflections exactly. -/
theorem celestialDelta_antiLinearShadow (s : ℂ) :
    celestialDelta (antiLinearShadow 1 s) =
      antiLinearShadow 2 (celestialDelta s) := by
  apply Complex.ext <;>
    simp [celestialDelta, antiLinearShadow, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- Therefore `Delta = 2s` transports the pointwise fixed arithmetic interface to
the pointwise fixed celestial interface without any spectral or zeta hypothesis. -/
theorem arithmetic_fixed_iff_celestial_fixed (s : ℂ) :
    antiLinearShadow 1 s = s ↔
      antiLinearShadow 2 (celestialDelta s) = celestialDelta s := by
  rw [arithmetic_antiLinearShadow_fixed_iff, celestial_antiLinearShadow_fixed_iff]
  exact (celestialDelta_re_eq_one_iff s).symm

end GppConformalShadowPrincipalSeries

#print axioms GppConformalShadowPrincipalSeries.conformalShadow_involutive
#print axioms GppConformalShadowPrincipalSeries.conformalShadow_eq_conj_iff
#print axioms GppConformalShadowPrincipalSeries.one_dimensional_shadow_eq_arithmetic
#print axioms GppConformalShadowPrincipalSeries.one_dimensional_shadow_eq_conj_iff
#print axioms GppConformalShadowPrincipalSeries.doubled_arithmetic_shadow_eq_two_dimensional
#print axioms GppConformalShadowPrincipalSeries.critical_line_iff_two_dimensional_principal
#print axioms GppConformalShadowPrincipalSeries.antiLinearShadow_involutive
#print axioms GppConformalShadowPrincipalSeries.antiLinearShadow_fixed_iff
#print axioms GppConformalShadowPrincipalSeries.arithmetic_antiLinearShadow_fixed_iff
#print axioms GppConformalShadowPrincipalSeries.celestial_antiLinearShadow_fixed_iff
#print axioms GppConformalShadowPrincipalSeries.celestialDelta_antiLinearShadow
#print axioms GppConformalShadowPrincipalSeries.arithmetic_fixed_iff_celestial_fixed
