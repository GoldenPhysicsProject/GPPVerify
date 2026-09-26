import GppVerify.RiemannHypothesis.CompletedZetaCriticalResponse
import GppVerify.CelestialHolography.PositiveRealPrincipalSeries
import GppVerify.CelestialHolography.PrincipalSeriesShadowConjugation
import Mathlib.Tactic

namespace GppCompletedZetaPrincipalSeriesResponse

open Complex
open GppPositiveReal

noncomputable def celestialCompletedResponse (Δ : ℂ) : ℂ :=
  deriv GppCompletedZetaDerivative.completedRiemannZeta (Δ / 2) /
    GppCompletedZetaDerivative.completedRiemannZeta (Δ / 2)

/-- Multiply the anti-Hermitian logarithmic response by `-i`. On the celestial
principal axis this is the real phase-generator normalization naturally associated
with a unitary scattering/transfer response. -/
noncomputable def celestialCompletedPhaseResponse (Δ : ℂ) : ℂ :=
  -Complex.I * celestialCompletedResponse Δ

theorem half_argument_re_eq_half {Δ : ℂ} (hΔ : Δ.re = 1) :
    (Δ / 2).re = 1 / 2 := by
  simp [Complex.div_re, hΔ]
  norm_num

theorem celestialCompletedResponse_re_eq_zero
    {Δ : ℂ} (hΔ : Δ.re = 1)
    (hΛ : GppCompletedZetaDerivative.completedRiemannZeta (Δ / 2) ≠ 0) :
    (celestialCompletedResponse Δ).re = 0 := by
  unfold celestialCompletedResponse
  exact GppCompletedZetaCriticalResponse.completedRiemannZeta_logDeriv_re_eq_zero_of_re_half
    (half_argument_re_eq_half hΔ) hΛ

/-- The `-i` normalized completed-zeta response is genuinely real on the celestial
principal-series axis, away from zeros where the logarithmic derivative is undefined. -/
theorem celestialCompletedPhaseResponse_im_eq_zero
    {Δ : ℂ} (hΔ : Δ.re = 1)
    (hΛ : GppCompletedZetaDerivative.completedRiemannZeta (Δ / 2) ≠ 0) :
    (celestialCompletedPhaseResponse Δ).im = 0 := by
  have hR := celestialCompletedResponse_re_eq_zero hΔ hΛ
  simp [celestialCompletedPhaseResponse, Complex.mul_im, hR]

/-- Under the exact dictionary `Δ = 2s`, the globally reflected logarithmic response
of completed zeta becomes an odd response under the scalar celestial shadow
`Δ ↦ 2 - Δ`.  The exclusions `Δ ≠ 0,2` are precisely the two completed-zeta poles,
and `hΛ` records the domain of the logarithmic derivative. -/
theorem celestialCompletedResponse_shadow_odd
    {Δ : ℂ} (hΔ0 : Δ ≠ 0) (hΔ2 : Δ ≠ 2)
    (hΛ : GppCompletedZetaDerivative.completedRiemannZeta (Δ / 2) ≠ 0) :
    celestialCompletedResponse Δ =
      -celestialCompletedResponse (celestialShadow Δ) := by
  have hs0 : Δ / 2 ≠ 0 := by
    exact div_ne_zero hΔ0 (by norm_num)
  have hs1 : Δ / 2 ≠ 1 := by
    intro hs
    apply hΔ2
    calc
      Δ = 2 * (Δ / 2) := by ring
      _ = 2 := by rw [hs]; ring
  have hreflect :=
    GppCompletedZetaDerivative.completedRiemannZeta_logDeriv_reflection hs0 hs1 hΛ
  have harg : 1 - Δ / 2 = celestialShadow Δ / 2 := by
    simp [celestialShadow]
    ring
  unfold celestialCompletedResponse
  rw [harg] at hreflect
  exact hreflect

/-- The real phase-generator normalization retains the same shadow oddness. -/
theorem celestialCompletedPhaseResponse_shadow_odd
    {Δ : ℂ} (hΔ0 : Δ ≠ 0) (hΔ2 : Δ ≠ 2)
    (hΛ : GppCompletedZetaDerivative.completedRiemannZeta (Δ / 2) ≠ 0) :
    celestialCompletedPhaseResponse Δ =
      -celestialCompletedPhaseResponse (celestialShadow Δ) := by
  unfold celestialCompletedPhaseResponse
  rw [celestialCompletedResponse_shadow_odd hΔ0 hΔ2 hΛ]
  ring

/-- **Principal-axis conjugation oddness.** On `Re Δ = 1`, scalar shadow is exactly
complex conjugation. Hence the completed-zeta logarithmic response is odd under
conjugation on the celestial principal-series axis. This is a direct combination
of functional-equation reflection with the positive-real half-density dictionary;
it makes no claim that a zero lies on this axis. -/
theorem celestialCompletedResponse_conj_odd_on_principal
    {Δ : ℂ} (hΔre : Δ.re = 1) (hΔ0 : Δ ≠ 0) (hΔ2 : Δ ≠ 2)
    (hΛ : GppCompletedZetaDerivative.completedRiemannZeta (Δ / 2) ≠ 0) :
    celestialCompletedResponse Δ =
      -celestialCompletedResponse (complexConj Δ) := by
  have hshadow : celestialShadow Δ = complexConj Δ :=
    GppPrincipalShadow.shadow_eq_conj_iff.mpr hΔre
  rw [← hshadow]
  exact celestialCompletedResponse_shadow_odd hΔ0 hΔ2 hΛ

/-- The real phase-generator normalization is likewise odd under conjugation on the
principal axis. Together with `celestialCompletedPhaseResponse_im_eq_zero`, this says
the principal-series completed-zeta response is a real odd phase response under the
shadow/conjugation involution, away from zeros. -/
theorem celestialCompletedPhaseResponse_conj_odd_on_principal
    {Δ : ℂ} (hΔre : Δ.re = 1) (hΔ0 : Δ ≠ 0) (hΔ2 : Δ ≠ 2)
    (hΛ : GppCompletedZetaDerivative.completedRiemannZeta (Δ / 2) ≠ 0) :
    celestialCompletedPhaseResponse Δ =
      -celestialCompletedPhaseResponse (complexConj Δ) := by
  have hshadow : celestialShadow Δ = complexConj Δ :=
    GppPrincipalShadow.shadow_eq_conj_iff.mpr hΔre
  rw [← hshadow]
  exact celestialCompletedPhaseResponse_shadow_odd hΔ0 hΔ2 hΛ

end GppCompletedZetaPrincipalSeriesResponse

#print axioms GppCompletedZetaPrincipalSeriesResponse.half_argument_re_eq_half
#print axioms GppCompletedZetaPrincipalSeriesResponse.celestialCompletedResponse_re_eq_zero
#print axioms GppCompletedZetaPrincipalSeriesResponse.celestialCompletedPhaseResponse_im_eq_zero
#print axioms GppCompletedZetaPrincipalSeriesResponse.celestialCompletedResponse_shadow_odd
#print axioms GppCompletedZetaPrincipalSeriesResponse.celestialCompletedPhaseResponse_shadow_odd
#print axioms GppCompletedZetaPrincipalSeriesResponse.celestialCompletedResponse_conj_odd_on_principal
#print axioms GppCompletedZetaPrincipalSeriesResponse.celestialCompletedPhaseResponse_conj_odd_on_principal
