import GppVerify.CelestialHolography.CompletedZetaSpectralAxis
import GppVerify.CelestialHolography.PrincipalSeriesDilationBridge
import Mathlib.Tactic

/-!
# Completed-zeta / dilation-unitarity bridge

This module packages the exact common spectral axis of three structures already
proved separately in the Codex/GPT construction:

* the positive-real half-density dilation representation;
* the celestial principal-series parameterization `Delta(tau) = 1 + 2 i tau`;
* the completed-zeta logarithmic phase response.

For `s(tau) = Delta(tau)/2 = 1/2 + i tau`, every nontrivial positive dilation
character has unit modulus.  Away from completed-zeta zeros, the `-i` normalized
logarithmic response is real and odd under `tau -> -tau`.

This is a representation-theoretic compatibility statement only.  It does not
assert that any zeta zero lies on the principal axis.
-/

namespace GppCompletedZetaDilationUnitaryBridge

open GppPositiveReal
open GppScaleMass
open GppPrincipalSeriesDilationBridge
open GppCompletedZetaPrincipalSeriesResponse
open GppCompletedZetaSpectralAxis

/-- The arithmetic Mellin parameter underlying `principalDelta tau` is exactly
`principalDelta tau / 2`, and transporting it by `Delta = 2s` returns the same
celestial principal-series point. -/
theorem celestialWeight_half_principalDelta (tau : ℝ) :
    celestialWeight (principalDelta tau / 2) = principalDelta tau := by
  unfold celestialWeight principalDelta
  ring

/-- Every parameterized celestial principal-series mode is unitary under the
half-density-normalized positive-real dilation character, at every fixed
nontrivial positive scale. -/
theorem principalDelta_dilation_unitary
    (tau : ℝ) {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) :
    ‖dilationCharacter (principalDelta tau / 2) a‖ = 1 := by
  apply (celestial_principal_iff_dilation_unitary
    (s := principalDelta tau / 2) ha ha1).mp
  rw [celestialWeight_half_principalDelta]
  exact principalDelta_re tau

/-- Exact synthesis on the common spectral axis.  For every real spectral
parameter and every nontrivial positive dilation scale, the half-density mode
is unitary.  Wherever the completed-zeta logarithmic derivative is defined, its
`-i` normalization is real and odd under spectral reflection. -/
theorem dilation_unitarity_and_completed_phase_response
    (tau : ℝ) {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1)
    (hLambda : GppCompletedZetaDerivative.completedRiemannZeta
      (principalDelta tau / 2) ≠ 0) :
    ‖dilationCharacter (principalDelta tau / 2) a‖ = 1 ∧
      (celestialCompletedPhaseResponse (principalDelta tau)).im = 0 ∧
      celestialCompletedPhaseResponse (principalDelta tau) =
        -celestialCompletedPhaseResponse (principalDelta (-tau)) := by
  refine ⟨principalDelta_dilation_unitary tau ha ha1, ?_, ?_⟩
  · exact celestialCompletedPhaseResponse_im_eq_zero_at_tau tau hLambda
  · exact celestialCompletedPhaseResponse_odd_tau tau hLambda

end GppCompletedZetaDilationUnitaryBridge

#print axioms GppCompletedZetaDilationUnitaryBridge.celestialWeight_half_principalDelta
#print axioms GppCompletedZetaDilationUnitaryBridge.principalDelta_dilation_unitary
#print axioms GppCompletedZetaDilationUnitaryBridge.dilation_unitarity_and_completed_phase_response
