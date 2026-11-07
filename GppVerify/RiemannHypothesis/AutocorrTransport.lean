import GppVerify.RiemannHypothesis.MeyerSpectralWeil
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Bridge transport lemmas: the autocorrelation stays in the test class and squares the transform

The Step 4 bridge spec (Turbo audit, revision 5 PASS, bridge
`MuseResearch/turbo-note-2026-11-07-bridge-blueprint-audit.md`) takes the autocorrelation as a
parameter with two named hypotheses. This module proves both for the repo's operation
`GppArithmeticReflection.autocorr g x = ∫ g(y) g(y − x) dy`:

* **(T1)** `isTestFunction_autocorr`: `IsTestFunction g → IsTestFunction (autocorr g)`.
  `autocorr g = g ⋆ (g ∘ neg)` is a convolution with a smooth compactly supported factor.
* **(T2)** `spectralTransform_autocorr`: `ĝ_auto(s) = ĝ(s) · ĝ(1 − s)`, by Fubini and the
  substitution `v = y − x`. At a zero `ρ` this is the paired-form summand with `c = ĝ`
  (for real `g`, `ĝ(1 − s) = conj ĝ(1 − s̄)`).

What the bridge still needs is the tail (a single test function's spectral sum runs over all
zeros), which requires the assembled explicit formula. No claim about RH.

Daniel Toupin / Golden Physics Project, with AI assistance from Turbo (spec, audit) and Claude
Code (Lean).
-/

namespace GppAutocorrTransport

open MeasureTheory Complex GppArithmeticReflection GppMeyerSpectralWeil
open scoped ContDiff Convolution

/-- The autocorrelation is the convolution `g ⋆ (g ∘ neg)`. -/
theorem autocorr_eq_convolution (g : ℝ → ℝ) :
    autocorr g = (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun t => g (-t)) := by
  funext x
  rw [convolution_mul]
  unfold autocorr
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [neg_sub]

/-- **(T1)** The autocorrelation of a test function is a test function. -/
theorem isTestFunction_autocorr {g : ℝ → ℝ} (hg : IsTestFunction g) :
    IsTestFunction (autocorr g) := by
  have hneg_c : HasCompactSupport (fun t : ℝ => g (-t)) := hg.2.comp_homeomorph (Homeomorph.neg ℝ)
  have hneg_d : ContDiff ℝ ∞ (fun t : ℝ => g (-t)) := hg.1.comp contDiff_neg
  rw [autocorr_eq_convolution]
  exact ⟨hneg_c.contDiff_convolution_right _ hg.1.continuous.locallyIntegrable hneg_d,
    hg.2.convolution _ hneg_c⟩

/-- The spectral integrand. -/
theorem integrable_spectral {g : ℝ → ℝ} (hg : IsTestFunction g) (s : ℂ) :
    Integrable (fun u : ℝ => (g u : ℂ) * Complex.exp ((s - 1 / 2) * u)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (continuous_ofReal.comp hg.1.continuous).mul
      (Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal))
  · exact (hg.2.comp_left Complex.ofReal_zero).mul_right

/-- **(T2)** The transform of the autocorrelation is `ĝ(s) ĝ(1 − s)`. -/
theorem spectralTransform_autocorr {g : ℝ → ℝ} (hg : IsTestFunction g) (s : ℂ) :
    spectralTransform (autocorr g) s = spectralTransform g s * spectralTransform g (1 - s) := by
  set a : ℂ := s - 1 / 2
  -- integrand on ℝ × ℝ : (x, y) ↦ g y g (y - x) e^{a x}
  set F : ℝ → ℝ → ℂ := fun x y => (g y : ℂ) * (g (y - x) : ℂ) * Complex.exp (a * x)
  have hcont : Continuous (Function.uncurry F) := by
    refine ((continuous_ofReal.comp (hg.1.continuous.comp continuous_snd)).mul
      (continuous_ofReal.comp (hg.1.continuous.comp (continuous_snd.sub continuous_fst)))).mul ?_
    exact Complex.continuous_exp.comp (continuous_const.mul (continuous_ofReal.comp continuous_fst))
  obtain ⟨R, hR⟩ : ∃ R, ∀ y, R < |y| → g y = 0 := by
    obtain ⟨R, hR⟩ := hg.2.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun y hy => ?_⟩
    by_contra h
    have : y ∈ tsupport g := subset_tsupport _ h
    have := hR this
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith
  have hsupp : HasCompactSupport (Function.uncurry F) := by
    refine HasCompactSupport.intro ((isCompact_closedBall (0 : ℝ) (2 * R)).prod
      (isCompact_closedBall (0 : ℝ) R)) (fun p hp => ?_)
    obtain ⟨x, y⟩ := p
    simp only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
      not_and_or, not_le] at hp
    simp only [Function.uncurry_apply_pair, F]
    rcases hp with hx | hy
    · by_cases hy : R < |y|
      · rw [hR y hy]; simp
      · have : R < |y - x| := by
          have := abs_sub_abs_le_abs_sub x y
          rw [abs_sub_comm] at this
          push Not at hy
          linarith
        rw [hR _ this]; simp
    · rw [hR y hy]; simp
  have hint : Integrable (Function.uncurry F) (volume.prod volume) :=
    hcont.integrable_of_hasCompactSupport hsupp
  unfold spectralTransform
  -- left side: ∫ x, (∫ y, g y g (y - x)) e^{a x} = ∫ x ∫ y F x y
  have hL : ∫ x : ℝ, ((autocorr g x : ℝ) : ℂ) * Complex.exp ((s - 1 / 2) * x) =
      ∫ x : ℝ, ∫ y : ℝ, F x y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [autocorr, F]
    rw [show ((∫ y, g y * g (y - x) : ℝ) : ℂ) = ∫ y, ((g y * g (y - x) : ℝ) : ℂ) from
      integral_ofReal.symm, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    push_cast; ring
  rw [hL, integral_integral_swap hint]
  -- inner integral over x for fixed y
  have hinner : ∀ y : ℝ, ∫ x : ℝ, F x y =
      (g y : ℂ) * Complex.exp (a * y) * ∫ v : ℝ, (g v : ℂ) * Complex.exp (((1 - s) - 1 / 2) * v) := by
    intro y
    rw [← integral_const_mul]
    rw [← integral_sub_left_eq_self (fun v : ℝ => (g y : ℂ) * Complex.exp (a * y) *
      ((g v : ℂ) * Complex.exp (((1 - s) - 1 / 2) * v))) volume y]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [F]
    have : Complex.exp (a * ↑x) =
        Complex.exp (a * ↑y) * Complex.exp (((1 - s) - 1 / 2) * ↑(y - x)) := by
      rw [← Complex.exp_add]; congr 1; simp only [a]; push_cast; ring
    rw [this]; ring
  simp_rw [hinner]
  rw [integral_mul_const]

end GppAutocorrTransport

#print axioms GppAutocorrTransport.isTestFunction_autocorr
#print axioms GppAutocorrTransport.spectralTransform_autocorr
