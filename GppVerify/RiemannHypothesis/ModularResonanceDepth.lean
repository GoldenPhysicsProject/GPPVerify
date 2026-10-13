import GppVerify.RiemannHypothesis.CompletedZetaReality

/-!
# Modular-surface zeta resonances sit at depth ¼, not on the unitary line

Source: Codex, GPPDiscovery2 `research/2026-09-27_modular_surface_arithmetic_ads2_scattering.md`,
§§3–4 (the correction to "zeta zeros = principal-series spectrum").

The cusp scattering coefficient of `PSL(2,ℤ)\ℍ` is `φ(w) = Λ(2w − 1)/Λ(2w)`, with `Λ` the completed
zeta function (Mathlib's `completedRiemannZeta`). Its unitarity on `Re w = ½` is already in
`ArithmeticEisensteinUnitarity`, under the reparametrization `Δ = 2w`. This file proves the
resonance bookkeeping. For a zero `ρ` of `ζ` with `0 < Re ρ < 1`:
* `denominator_zero`: `Λ(2 · ρ/2) = 0`, so `w = ρ/2` is a pole of `φ`. It is never on the unitary
  line: `Re(ρ/2) < ½` (`pole_re_lt_half`).
* `numerator_zero`: `Λ(2 · (ρ+1)/2 − 1) = 0`, so `(ρ+1)/2` is a zero of `φ`.
* `reflection`: the partner zero `1 − ρ` puts its numerator zero at `1 − ρ/2`, the image of the
  pole under `w ↦ 1 − w`.
* `depth_eq_quarter_iff`: the depth `½ − Re(ρ/2)` equals `¼` iff `Re ρ = ½`.

So RH is equivalent to a *uniform resonance depth ¼* for the modular-surface zeta resonances, not to
those resonances lying on the Laplacian's principal-series line. The identification "zeros =
principal-series spectrum" holds only in the zeta variable `s`, never in the Eisenstein parameter
`w`. **No RH claim.**
-/

namespace GppModularResonanceDepth

theorem completed_zero_of_zeta_zero {ρ : ℂ} (h0 : 0 < ρ.re) (hz : riemannZeta ρ = 0) :
    completedRiemannZeta ρ = 0 := by
  rw [GppCompletedZetaReality.completedZeta_eq_GammaR_mul_zeta h0, hz, mul_zero]

/-- The modular cusp scattering coefficient `φ(w) = Λ(2w − 1)/Λ(2w)`. -/
noncomputable def phi (w : ℂ) : ℂ := completedRiemannZeta (2 * w - 1) / completedRiemannZeta (2 * w)

theorem denominator_zero {ρ : ℂ} (h0 : 0 < ρ.re) (hz : riemannZeta ρ = 0) :
    completedRiemannZeta (2 * (ρ / 2)) = 0 := by
  rw [mul_div_cancel₀ ρ two_ne_zero]; exact completed_zero_of_zeta_zero h0 hz

theorem numerator_zero {ρ : ℂ} (h0 : 0 < ρ.re) (hz : riemannZeta ρ = 0) :
    completedRiemannZeta (2 * ((ρ + 1) / 2) - 1) = 0 := by
  have : 2 * ((ρ + 1) / 2) - 1 = ρ := by ring
  rw [this]; exact completed_zero_of_zeta_zero h0 hz

theorem pole_re_lt_half {ρ : ℂ} (h1 : ρ.re < 1) : (ρ / 2).re < 1 / 2 := by
  rw [Complex.div_ofNat_re]; linarith

/-- The partner zero `1 − ρ` puts its numerator zero at `1 − ρ/2`, the reflection of the pole. -/
theorem reflection (ρ : ℂ) : ((1 - ρ) + 1) / 2 = 1 - ρ / 2 := by ring

theorem partner_numerator_zero {ρ : ℂ} (h0 : 0 < ρ.re) (hz : riemannZeta ρ = 0) :
    completedRiemannZeta (2 * (1 - ρ / 2) - 1) = 0 := by
  have : 2 * (1 - ρ / 2) - 1 = 1 - ρ := by ring
  rw [this, completedRiemannZeta_one_sub]; exact completed_zero_of_zeta_zero h0 hz

/-- **Uniform depth**: `½ − Re(ρ/2) = ¼ ↔ Re ρ = ½`. -/
theorem depth_eq_quarter_iff (ρ : ℂ) : 1 / 2 - (ρ / 2).re = 1 / 4 ↔ ρ.re = 1 / 2 := by
  rw [Complex.div_ofNat_re]; constructor <;> intro h <;> linarith

end GppModularResonanceDepth
