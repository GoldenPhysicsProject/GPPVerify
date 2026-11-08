/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Principal series)
-/
import GppVerify.RiemannHypothesis.LocalTateEvaluations
import GppVerify.NoGo.HermiteFourierIndefinite
import Mathlib.Data.Real.Sign
import Mathlib.Tactic.FinCases

/-!
# The real Tate parity test vectors

For the two Tate parities, evaluate the Gaussian/Hermite-Gaussian zeta integrals
and their actual Fourier transforms, then derive the local functional equation
**only for these test vectors**. Mathlib uses the kernel `exp(-2πixy)` and
Lebesgue measure; the multiplicative integral is written as `|x|^(s-1) dx`,
without an extra factor of one half. The phases are `+1` and `-i`, distinct from
the full gamma ratio.

Governing specification: Turbo, GPP-bridge
`MuseResearch/turbo-note-2026-11-07-grh-d-formalization-spec.md` at `64a43efe`, §1.
The evaluations reuse Claude Code's `LocalTateEvaluations` (#499; Gemini blueprint,
Turbo audit). The Fourier calculations reuse Codex's
`GppNoGo.HermiteFourierIndefinite` (see that module's source attribution).

No arbitrary-Schwartz-function Tate functional equation, continuous CFT shift,
sector construction, global positivity, or RH/GRH conclusion is proved here.
-/

open MeasureTheory Complex FourierTransform
open scoped Real

namespace LocalTate.Archimedean

/-- The shifted real gamma factor, restricted to the two Tate parities. -/
noncomputable def archFactor (a : Fin 2) (s : ℂ) : ℂ := Gammaℝ (s + a.val)

/-- The constant Fourier phase: `+1` even, `-i` odd, not the full gamma ratio. -/
def archPhase (a : Fin 2) : ℂ := (-I) ^ a.val

/-- Gaussian at even parity, `x` times the same Gaussian at odd parity. -/
noncomputable def testVector (a : Fin 2) (x : ℝ) : ℂ :=
  (x : ℂ) ^ a.val * (gaussian x : ℂ)

/-- Tate's sign-character integral against `dx/|x|`, using additive Lebesgue measure.
Values assigned at zero do not affect this integral. -/
noncomputable def parityZeta (a : Fin 2) (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, f x * (Real.sign x : ℂ) ^ a.val * ((|x| : ℝ) : ℂ) ^ (s - 1)

/-- Multiplication by the sign character changes the odd moment to an absolute moment.
The equality is a.e.; at zero, totalized complex powers can have different values. -/
theorem parityZeta_testVector_eq_localZeta (a : Fin 2) (s : ℂ) :
    parityZeta a (testVector a) s = localZeta (s + a.val) := by
  unfold parityZeta localZeta
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> decide) with rfl | rfl
  · simp [testVector]
  · simp only [testVector, Fin.val_one, pow_one, Nat.cast_one]
    change ((x : ℂ) * (gaussian x : ℂ)) * (Real.sign x : ℂ) *
        ((|x| : ℝ) : ℂ) ^ (s - 1) =
      (gaussian x : ℂ) * ((|x| : ℝ) : ℂ) ^ (s + 1 - 1)
    have hsign : (x : ℂ) * (Real.sign x : ℂ) = (|x| : ℝ) := by
      have hr : x * Real.sign x = |x| := by
        obtain hn | rfl | hp := lt_trichotomy x 0
        · rw [Real.sign_of_neg hn, abs_of_neg hn]; ring
        · simp
        · rw [Real.sign_of_pos hp, abs_of_pos hp]; ring
      exact_mod_cast hr
    have habs : ((|x| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (abs_ne_zero.mpr hx)
    rw [show s + 1 - 1 = (s - 1) + 1 by ring, cpow_add _ _ habs, cpow_one]
    calc
      _ = (gaussian x : ℂ) * ((x : ℂ) * (Real.sign x : ℂ)) *
          ((|x| : ℝ) : ℂ) ^ (s - 1) := by ring
      _ = _ := by rw [hsign]; ring

/-- Both parity moments, normalized to Mathlib's `Gammaℝ`.
The odd integral converges already for `Re s > -1`. -/
theorem parityZeta_testVector (a : Fin 2) {s : ℂ}
    (hs : 0 < (s + (a.val : ℂ)).re) :
    parityZeta a (testVector a) s = archFactor a s := by
  rw [parityZeta_testVector_eq_localZeta, archimedean_evaluation_Gammaℝ hs]
  rfl

/-- Nonvanishing on the actual moment-convergence half-plane. -/
theorem archFactor_ne_zero (a : Fin 2) {s : ℂ}
    (hs : 0 < (s + (a.val : ℂ)).re) : archFactor a s ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos hs

/-- Actual Bochner integrability, not merely a totalized integral identity. -/
theorem integrable_parityZeta_testVector (a : Fin 2) {s : ℂ}
    (hs : 0 < (s + (a.val : ℂ)).re) :
    Integrable (fun x : ℝ => testVector a x * (Real.sign x : ℂ) ^ a.val *
      ((|x| : ℝ) : ℂ) ^ (s - 1)) := by
  apply Integrable.of_integral_ne_zero
  change parityZeta a (testVector a) s ≠ 0
  rw [parityZeta_testVector a hs]
  exact archFactor_ne_zero a hs

/-- Both constant phases are unitary. -/
theorem norm_archPhase (a : Fin 2) : ‖archPhase a‖ = 1 := by
  simp [archPhase]

private theorem gaussian_complex (x : ℝ) :
    (gaussian x : ℂ) = GppNoGo.HermiteFourierIndefinite.g x := by
  simp [gaussian, GppNoGo.HermiteFourierIndefinite.g, ofReal_exp]

/-- The test vectors themselves are integrable for the additive Fourier transform. -/
theorem integrable_testVector (a : Fin 2) : Integrable (testVector a) := by
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> decide) with rfl | rfl
  · exact GppNoGo.HermiteFourierIndefinite.integrable_g.congr
      (Filter.Eventually.of_forall fun x => by simp [testVector, gaussian_complex])
  · exact GppNoGo.HermiteFourierIndefinite.integrable_xg.congr
      (Filter.Eventually.of_forall fun x => by simp [testVector, gaussian_complex])

/-- Actual Fourier eigenvectors for the negative-exponent Fourier convention. -/
theorem fourier_testVector (a : Fin 2) :
    𝓕 (testVector a) = fun x => archPhase a * testVector a x := by
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> decide) with rfl | rfl
  · have h : testVector 0 = GppNoGo.HermiteFourierIndefinite.g := by
      funext x
      simp [testVector, gaussian_complex]
    simpa [archPhase, h] using GppNoGo.HermiteFourierIndefinite.fourier_g
  · let c : ℂ := (-2 * (Real.pi : ℂ))⁻¹
    have h : testVector 1 = c • GppNoGo.HermiteFourierIndefinite.g1 := by
      funext x
      simp only [testVector, Fin.val_one, pow_one, Pi.smul_apply, smul_eq_mul,
        GppNoGo.HermiteFourierIndefinite.g1]
      change (x : ℂ) * (gaussian x : ℂ) =
        c * (-2 * (Real.pi : ℂ) * (x : ℂ) * GppNoGo.HermiteFourierIndefinite.g x)
      rw [gaussian_complex]
      have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      dsimp [c]
      field_simp [hpi]
    have hsmul : 𝓕 (c • GppNoGo.HermiteFourierIndefinite.g1) =
        c • 𝓕 GppNoGo.HermiteFourierIndefinite.g1 :=
      VectorFourier.fourierIntegral_const_smul 𝐞 volume (innerₗ ℝ) _ c
    rw [h, hsmul]
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [GppNoGo.HermiteFourierIndefinite.fourier_g1]
    simp only [archPhase, Fin.val_one, pow_one, GppNoGo.HermiteFourierIndefinite.g1]
    ring

/-- Scalar linearity of the sign-character integral. -/
theorem parityZeta_const_mul (a : Fin 2) (f : ℝ → ℂ) (s c : ℂ) :
    parityZeta a (fun x => c * f x) s = c * parityZeta a f s := by
  unfold parityZeta
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

/-- The cross-multiplied local FE for the two actual test vectors, on the common strip.
This is not the Tate FE for arbitrary Schwartz functions. -/
theorem localFE_testVector (a : Fin 2) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    archFactor a s * parityZeta a (𝓕 (testVector a)) (1 - s) =
      archPhase a * archFactor a (1 - s) * parityZeta a (testVector a) s := by
  have ha : (0 : ℝ) ≤ a.val := Nat.cast_nonneg _
  have hpos : 0 < (s + (a.val : ℂ)).re := by
    simp only [add_re, natCast_re]
    linarith
  have hdual : 0 < (1 - s + (a.val : ℂ)).re := by
    simp only [add_re, sub_re, one_re, natCast_re]
    linarith
  rw [fourier_testVector, parityZeta_const_mul,
    parityZeta_testVector a hdual, parityZeta_testVector a hpos]
  ring

/-- The Step 1 integrability residual, under its blueprint name: `e^{-πx²}|x|^{s-1}` is
Bochner integrable on `Re s > 0`. This is `integrable_parityZeta_testVector` at the even
parity `a = 0` (Step 1 blueprint, GPP-bridge `turbo-note-2026-11-06-step1-blueprint-revised.md`;
closed 2026-11-08 at Turbo's request, PR11 6724419374). -/
theorem localZeta_integrable {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun x : ℝ => (gaussian x : ℂ) * ((|x| : ℝ) : ℂ) ^ (s - 1)) := by
  have h := integrable_parityZeta_testVector (0 : Fin 2) (s := s) (by simpa using hs)
  simpa [testVector] using h

end LocalTate.Archimedean
