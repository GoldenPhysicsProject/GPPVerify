/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.ArchimedeanTateParity
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.MellinTransform

/-!
# Schwartz Tate local theory: integrability (W1, W2, F1)

For every Schwartz function `f : 𝓢(ℝ, ℂ)`, both Tate characters and every `s` with
`0 < Re s`, the additive integrand of `parityZeta` is Bochner integrable. The singularity
at the origin (W1) is handled by boundedness of `f` against the integrable weight
`|x|^(Re s - 1)`; the tails (W2) by Schwartz decay. The same holds for the Schwartz
Fourier transform `𝓕 f` (F1), so on `0 < Re s < 1` both sides of the local functional
equation are absolutely convergent.

Governing specification: Principal Series's Schwartz Tate statement sheet
(GPP-bridge `5fa0d320`, obligations W1/W2/F1), audited PASS by Turbo (`1d8e695`).
-/

open MeasureTheory Complex Asymptotics Filter Set
open scoped Topology FourierTransform SchwartzMap

namespace LocalTate.Archimedean

/-- A continuous function decaying faster than every power has a convergent Mellin
integral on `0 < Re s`. -/
theorem mellinConvergent_of_rapid_decay {g : ℝ → ℂ} (hc : Continuous g)
    (hdec : ∀ r : ℝ, g =O[cocompact ℝ] (‖·‖ ^ r)) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent g s := by
  refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 0)
    (hc.locallyIntegrable.locallyIntegrableOn _) ?_ (by linarith) ?_ hs
  · refine ((hdec (-(s.re + 1))).mono atTop_le_cocompact).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.norm_of_nonneg hx.le]
  · have h1 : g =O[𝓝[>] (0 : ℝ)] (fun _ => (1 : ℝ)) :=
      ((hc.tendsto 0).isBigO_one ℝ).mono nhdsWithin_le_nhds
    refine h1.congr' EventuallyEq.rfl (Eventually.of_forall fun x => ?_)
    simp

/-- Rapid decay is preserved by reflection. -/
theorem rapid_decay_comp_neg {g : ℝ → ℂ} (hdec : ∀ r : ℝ, g =O[cocompact ℝ] (‖·‖ ^ r))
    (r : ℝ) : (fun x => g (-x)) =O[cocompact ℝ] (‖·‖ ^ r) := by
  have ht : Tendsto (fun x : ℝ => -x) (cocompact ℝ) (cocompact ℝ) :=
    ((Homeomorph.neg ℝ).map_cocompact).le
  simpa [Function.comp_def] using (hdec r).comp_tendsto ht

/-- The additive Tate integrand of a continuous rapidly decaying function is Bochner
integrable on `0 < Re s`, for both characters (W1 at the origin, W2 at infinity). -/
theorem integrable_parityZeta_of_rapid_decay {g : ℝ → ℂ} (hc : Continuous g)
    (hdec : ∀ r : ℝ, g =O[cocompact ℝ] (‖·‖ ^ r)) (a : Fin 2) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun x : ℝ => g x * (Real.sign x : ℂ) ^ a.val * ((|x| : ℝ) : ℂ) ^ (s - 1)) := by
  set F : ℝ → ℂ := fun x => g x * (Real.sign x : ℂ) ^ a.val * ((|x| : ℝ) : ℂ) ^ (s - 1)
  have hpos : IntegrableOn F (Ioi 0) := by
    refine (mellinConvergent_of_rapid_decay hc hdec hs).congr_fun (fun x hx => ?_)
      measurableSet_Ioi
    have hx : (0 : ℝ) < x := hx
    simp [F, Real.sign_of_pos hx, abs_of_pos hx, mul_comm]
  have hneg : IntegrableOn F (Iio 0) := by
    have hm := (mellinConvergent_of_rapid_decay (hc.comp continuous_neg)
      (rapid_decay_comp_neg hdec) hs).const_mul (((-1 : ℂ)) ^ a.val)
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Iio 0 = Ioi 0 := by ext x; simp
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding, hpre]
    refine IntegrableOn.congr_fun hm (fun x hx => ?_) measurableSet_Ioi
    have hx : (0 : ℝ) < x := hx
    have hx' : -x < 0 := neg_neg_of_pos hx
    simp [F, Real.sign_of_neg hx', abs_of_neg hx']
    ring
  have hIic : IntegrableOn F (Iic 0) := (integrableOn_Iic_iff_integrableOn_Iio).2 hneg
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hpos

/-- **W1 + W2.** For every Schwartz `f`, both characters and `0 < Re s`, the additive
integrand defining `parityZeta a f s` is Bochner integrable. -/
theorem schwartz_parityZeta_integrable (f : 𝓢(ℝ, ℂ)) (a : Fin 2) {s : ℂ}
    (hs : 0 < s.re) :
    Integrable (fun x : ℝ => f x * (Real.sign x : ℂ) ^ a.val * ((|x| : ℝ) : ℂ) ^ (s - 1)) :=
  integrable_parityZeta_of_rapid_decay f.continuous f.isBigO_cocompact_rpow a hs

/-- **F1.** The same integrability for the function-level Fourier transform `𝓕 f`
(negative-exponent kernel, Lebesgue measure), through Schwartz closure of `𝓕`. -/
theorem schwartz_fourier_parityZeta_integrable (f : 𝓢(ℝ, ℂ)) (a : Fin 2) {s : ℂ}
    (hs : 0 < s.re) :
    Integrable (fun x : ℝ => 𝓕 (f : ℝ → ℂ) x * (Real.sign x : ℂ) ^ a.val *
      ((|x| : ℝ) : ℂ) ^ (s - 1)) := by
  simpa [SchwartzMap.fourier_coe] using schwartz_parityZeta_integrable (𝓕 f) a hs

/-- On the common strip `0 < Re s < 1`, both sides of the local functional equation
are absolutely convergent: `Z(f, s)` and `Z(𝓕 f, 1 - s)`. -/
theorem schwartz_localFE_sides_integrable (f : 𝓢(ℝ, ℂ)) (a : Fin 2) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Integrable (fun x : ℝ => f x * (Real.sign x : ℂ) ^ a.val * ((|x| : ℝ) : ℂ) ^ (s - 1)) ∧
    Integrable (fun x : ℝ => 𝓕 (f : ℝ → ℂ) x * (Real.sign x : ℂ) ^ a.val *
      ((|x| : ℝ) : ℂ) ^ ((1 - s) - 1)) :=
  ⟨schwartz_parityZeta_integrable f a hs0,
    schwartz_fourier_parityZeta_integrable f a (by simp; linarith)⟩

end LocalTate.Archimedean
