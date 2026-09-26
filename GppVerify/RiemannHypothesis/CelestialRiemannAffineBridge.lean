import GppVerify.RiemannHypothesis.ScaleShadowHalfDensity
import Mathlib.Tactic

/-!
# Exact affine bridge between the Riemann and celestial principal lines

This file formalizes only the coordinate dictionary `Delta = 2 s`:

* `s -> 1-s` becomes `Delta -> 2-Delta`;
* `Re s = 1/2` becomes `Re Delta = 1`;
* `s = 1/2 + i t` becomes `Delta = 1 + 2 i t`.

These are representation-theoretic/algebraic identities. They contain no statement
about zeta zeros and do not prove RH.
-/

namespace GppCelestialRiemannAffine

open Complex

/-- Project dictionary from the one-dimensional Riemann Mellin coordinate to the
two-dimensional celestial conformal dimension. -/
def celestialDelta (s : ℂ) : ℂ := 2 * s

/-- The Riemann reflection becomes the celestial scalar shadow exactly. -/
theorem celestialDelta_shadow (s : ℂ) :
    celestialDelta (1 - s) = 2 - celestialDelta s := by
  unfold celestialDelta
  ring

/-- The Riemann critical real part is exactly the celestial principal-series real part. -/
theorem critical_line_iff_celestial_principal_line (s : ℂ) :
    s.re = (1 / 2 : ℝ) ↔ (celestialDelta s).re = 1 := by
  unfold celestialDelta
  simp only [mul_re, ofNat_re, ofNat_im, zero_mul, sub_zero]
  constructor <;> intro h
  · linarith
  · linarith

/-- On the centered parametrization, `Delta=2s` doubles the spectral coordinate. -/
theorem celestialDelta_centered (t : ℝ) :
    celestialDelta ((1 / 2 : ℂ) + t * Complex.I) =
      1 + (2 * t) * Complex.I := by
  unfold celestialDelta
  push_cast
  ring

/-- Shadow on the Riemann line corresponds to reversing the celestial spectral sign. -/
theorem celestial_shadow_centered (t : ℝ) :
    celestialDelta (1 - ((1 / 2 : ℂ) + t * Complex.I)) =
      1 - (2 * t) * Complex.I := by
  rw [celestialDelta_shadow, celestialDelta_centered]
  ring

end GppCelestialRiemannAffine

#print axioms GppCelestialRiemannAffine.celestialDelta_shadow
#print axioms GppCelestialRiemannAffine.critical_line_iff_celestial_principal_line
#print axioms GppCelestialRiemannAffine.celestialDelta_centered
