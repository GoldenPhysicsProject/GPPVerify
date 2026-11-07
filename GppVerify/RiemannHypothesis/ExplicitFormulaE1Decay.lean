import GppVerify.RiemannHypothesis.MeyerSpectralWeil
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Explicit formula, stage E1: rapid decay of the spectral transform on vertical lines

Layer 1.5 of the full-construction brief (plan:
bridge `MuseResearch/claude-code-note-2026-11-07-explicit-formula-plan.md`). For a test
function `g` (smooth, compact support, log variable) the spectral transform
`ĝ(s) = ∫ g(u) e^{(s − 1/2) u} du` decays faster than every power of `t` along each
vertical line `s = σ + i t`:

  `∀ σ k, ∃ C, ∀ t, |t|^k ‖ĝ(σ + i t)‖ ≤ C`   (`spectralTransform_decay`).

Proof: `u ↦ g(u) e^{(σ − 1/2) u}` is smooth with compact support, hence Schwartz
(`HasCompactSupport.toSchwartzMap`); on the line `Re s = σ` the spectral transform is its
Fourier transform at `−t/2π` (`spectralTransform_eq_fourier`); the Fourier transform of a
Schwartz function is Schwartz, and Schwartz seminorms bound `|x|^k |F(x)|`.

This is the input the contour-shift proof needs to make the integrals over vertical lines
and the sum over zeros converge. Uniformity in `σ` over a compact interval is not proved
here (stage E1b if needed). No claim about RH.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.
-/

namespace GppExplicitFormulaE1

open MeasureTheory Complex SchwartzMap FourierTransform GppMeyerSpectralWeil
open scoped ContDiff

/-- `u ↦ g(u) e^{(σ − 1/2) u}`. -/
noncomputable def shifted (g : ℝ → ℝ) (σ : ℝ) : ℝ → ℂ :=
  fun u => (g u : ℂ) * Complex.exp (((σ : ℂ) - 1 / 2) * u)

theorem shifted_hasCompactSupport {g : ℝ → ℝ} (hg : HasCompactSupport g) (σ : ℝ) :
    HasCompactSupport (shifted g σ) :=
  (hg.comp_left Complex.ofReal_zero).mul_right

theorem shifted_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (σ : ℝ) :
    ContDiff ℝ ∞ (shifted g σ) :=
  (Complex.ofRealCLM.contDiff.comp hg).mul
    (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff))

/-- The shifted test function as a Schwartz function. -/
noncomputable def shiftedSchwartz {g : ℝ → ℝ} (hg : IsTestFunction g) (σ : ℝ) : 𝓢(ℝ, ℂ) :=
  (shifted_hasCompactSupport hg.2 σ).toSchwartzMap (shifted_contDiff hg.1 σ)

/-- On the line `Re s = σ` the spectral transform is a Fourier transform. -/
theorem spectralTransform_eq_fourier {g : ℝ → ℝ} (hg : IsTestFunction g) (σ t : ℝ) :
    spectralTransform g ((σ : ℂ) + t * I) = (𝓕 (shiftedSchwartz hg σ)) (-t / (2 * Real.pi)) := by
  rw [fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  unfold spectralTransform
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hS : (shiftedSchwartz hg σ) u = shifted g σ u := rfl
  simp only [smul_eq_mul]
  rw [hS]
  unfold shifted
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- **E1: rapid decay on vertical lines.** -/
theorem spectralTransform_decay {g : ℝ → ℝ} (hg : IsTestFunction g) (σ : ℝ) (k : ℕ) :
    ∃ C, ∀ t : ℝ, |t| ^ k * ‖spectralTransform g ((σ : ℂ) + t * I)‖ ≤ C := by
  set F := 𝓕 (shiftedSchwartz hg σ)
  refine ⟨(2 * Real.pi) ^ k * SchwartzMap.seminorm ℂ k 0 F, fun t => ?_⟩
  have h := norm_pow_mul_le_seminorm ℂ F k (-t / (2 * Real.pi))
  rw [spectralTransform_eq_fourier hg]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hn : ‖(-t / (2 * Real.pi) : ℝ)‖ = |t| / (2 * Real.pi) := by
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hpi]
  rw [hn, div_pow] at h
  have e : |t| ^ k * ‖F (-t / (2 * Real.pi))‖ =
      (2 * Real.pi) ^ k * (|t| ^ k / (2 * Real.pi) ^ k * ‖F (-t / (2 * Real.pi))‖) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h (by positivity)

end GppExplicitFormulaE1

#print axioms GppExplicitFormulaE1.spectralTransform_decay
